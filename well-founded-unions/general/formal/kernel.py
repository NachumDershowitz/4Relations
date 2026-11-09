"""Small proof-certificate checker for classical simple type theory.

Only natural-deduction inferences, beta/alpha conversion and type instantiation
are trusted.  No mathematical theorem or induction principle is an axiom.
The only non-intuitionistic rule is excluded middle.  Quantification includes
predicate/function types. All derivations retain their undischarged assumptions.
"""
from __future__ import annotations
from functools import lru_cache
from dataclasses import dataclass
import json

O = 'o'
def Arr(a,b): return ('->',a,b)
def V(n,t): return ('v',n,t)
def App(f,x): return ('app',f,x)
def Lam(v,b): return ('lam',v,b)
def All(v,b): return ('all',v,b)
def Ex(v,b): return ('ex',v,b)
def Imp(a,b): return ('imp',a,b)
def And(a,b): return ('and',a,b)
def Or(a,b): return ('or',a,b)
Bot=('bot',)
def Not(a): return Imp(a,Bot)

class CheckError(Exception): pass

def require(b,msg):
    if not b: raise CheckError(msg)

@lru_cache(None)
def type_of(t):
    tag=t[0]
    if tag=='v':
        require(is_type(t[2]), 'invalid variable type')
        return t[2]
    if tag=='bot': return O
    if tag=='app':
        f,x=t[1:]; tf=type_of(f)
        require(isinstance(tf,tuple) and len(tf)==3 and tf[0]=='->', 'app nonfunction')
        require(type_of(x)==tf[1], 'application type mismatch: '+str((tf,type_of(x))))
        return tf[2]
    if tag=='lam':
        require(t[1][0]=='v','lambda binder must be variable')
        return Arr(type_of(t[1]),type_of(t[2]))
    if tag in ('all','ex'):
        require(t[1][0]=='v','binder must be variable')
        type_of(t[1]); require(type_of(t[2])==O, 'quantified body not proposition')
        return O
    if tag in ('imp','and','or'):
        require(type_of(t[1])==type_of(t[2])==O,'connective argument not proposition')
        return O
    raise CheckError('unknown term tag '+str(tag))

def is_type(t):
    return (isinstance(t,str) and len(t)>0) or (isinstance(t,tuple) and len(t)==3 and t[0]=='->' and is_type(t[1]) and is_type(t[2]))

@lru_cache(None)
def fv(t):
    if t[0]=='v': return frozenset((t,))
    if t[0]=='bot': return frozenset()
    if t[0] in ('lam','all','ex'): return fv(t[2])-{t[1]}
    return fv(t[1])|fv(t[2])

@lru_cache(None)
def all_variables(t):
    if t[0]=='v':return frozenset((t,))
    if t[0]=='bot':return frozenset()
    return all_variables(t[1]) | all_variables(t[2])

_counter=0
def fresh(t,prefix='v'):
    global _counter
    _counter+=1
    return V(prefix+'#'+str(_counter),t)

@lru_cache(None)
def subst(t,v,u):
    require(v[0]=='v','substitution variable')
    require(type_of(v)==type_of(u),'substitution type mismatch')
    if t==v: return u
    if t[0] in ('v','bot'): return t
    if t[0] in ('lam','all','ex'):
        w,b=t[1:]
        if w==v: return t
        if w in fv(u) and v in fv(b):
            w2=fresh(type_of(w),'alpha')
            avoid=all_variables(b)|all_variables(u)|{v,w}
            while w2 in avoid:w2=fresh(type_of(w),'alpha')
            b=subst(b,w,w2); w=w2
        return (t[0],w,subst(b,v,u))
    return (t[0],subst(t[1],v,u),subst(t[2],v,u))

@lru_cache(None)
def norm(t):
    if t[0] in ('v','bot'): return t
    if t[0] in ('all','ex','lam'): return (t[0],t[1],norm(t[2]))
    a,b=norm(t[1]),norm(t[2])
    if t[0]=='app' and a[0]=='lam': return norm(subst(a[2],a[1],b))
    return (t[0],a,b)

@lru_cache(None)
def alpha(t,env=()):
    if t[0]=='v':
        if t in env: return ('bound',env[::-1].index(t),t[2])
        return t
    if t[0]=='bot': return t
    if t[0] in ('all','ex','lam'): return (t[0],t[1][2],alpha(t[2],env+(t[1],)))
    return (t[0],alpha(t[1],env),alpha(t[2],env))

def key(t): return alpha(norm(t))
def same(a,b): return key(a)==key(b)
def proposition(t): require(type_of(t)==O,'not a proposition')

def ty_sub(t,m):
    if isinstance(t,str): return m.get(t,t) if t!='o' else t
    return Arr(ty_sub(t[1],m),ty_sub(t[2],m))
def type_sub(t,m,env=None,used=None):
    if env is None: env={}
    if used is None: used={V(v[1],ty_sub(v[2],m)) for v in all_variables(t)}
    if t[0]=='v': return env.get(t,V(t[1],ty_sub(t[2],m)))
    if t[0]=='bot': return t
    if t[0] in ('all','ex','lam'):
        w=fresh(ty_sub(t[1][2],m),'typebind')
        while w in used:w=fresh(ty_sub(t[1][2],m),'typebind')
        used.add(w)
        en=dict(env);en[t[1]]=w
        return (t[0],w,type_sub(t[2],m,en,used))
    return (t[0],type_sub(t[1],m,env,used),type_sub(t[2],m,env,used))

@dataclass(frozen=True)
class Judgment:
    # Assumptions canonicalized by beta/alpha conversion.
    assumptions: tuple
    conclusion: tuple

def union(*hs):
    d={}
    for h in hs:
        for a in h: d[key(a)]=a
    return tuple(d[k] for k in sorted(d,key=repr))
def remove(h,a): return tuple(x for x in h if not same(x,a))
def free_hyps(h):
    r=set()
    for a in h:r.update(fv(a))
    return r

class Kernel:
    def __init__(self): self.proofs=[]; self.records=[]
    def add(self,rule,refs=(),args=()):
        require(all(isinstance(i,int) and 0<=i<len(self.proofs) for i in refs),'forward/invalid proof reference')
        ps=[self.proofs[i] for i in refs]
        def arity(n,m): require(len(ps)==n and len(args)==m,'wrong rule arity: '+rule)
        if rule=='assume':
            arity(0,1); a=args[0]; proposition(a); h=(a,); c=a
        elif rule=='imp_i':
            arity(1,1); a=args[0]; proposition(a); h=remove(ps[0].assumptions,a); c=Imp(a,ps[0].conclusion)
        elif rule=='imp_e':
            arity(2,0); p,q=ps; f=norm(p.conclusion); require(f[0]=='imp','imp_e nonimplication'); require(same(f[1],q.conclusion),'imp_e mismatch')
            h=union(p.assumptions,q.assumptions); c=f[2]
        elif rule=='and_i':
            arity(2,0); h=union(*(p.assumptions for p in ps)); c=And(*(p.conclusion for p in ps))
        elif rule in ('and_l','and_r'):
            arity(1,0); f=norm(ps[0].conclusion); require(f[0]=='and','conjunction projection');h=ps[0].assumptions;c=f[1 if rule=='and_l' else 2]
        elif rule in ('or_l','or_r'):
            arity(1,1); proposition(args[0]); h=ps[0].assumptions
            c=Or(ps[0].conclusion,args[0]) if rule=='or_l' else Or(args[0],ps[0].conclusion)
        elif rule=='or_e':
            arity(3,0); p,q,r=ps; f=norm(p.conclusion);require(f[0]=='or','or_e nondisjunction'); require(same(q.conclusion,r.conclusion),'or_e differing conclusions')
            h=union(p.assumptions,remove(q.assumptions,f[1]),remove(r.assumptions,f[2]));c=q.conclusion
        elif rule=='all_i':
            arity(1,1); v=args[0]; require(v[0]=='v','all_i binder'); require(v not in free_hyps(ps[0].assumptions),'all_i eigenvariable in assumptions')
            h=ps[0].assumptions;c=All(v,ps[0].conclusion)
        elif rule=='all_e':
            arity(1,1); f=norm(ps[0].conclusion);require(f[0]=='all','all_e nonuniversal');u=args[0];require(type_of(u)==type_of(f[1]),'all_e type mismatch')
            h=ps[0].assumptions;c=subst(f[2],f[1],u)
        elif rule=='ex_i':
            arity(1,2); f,u=args; require(f[0]=='ex','ex_i target'); proposition(f); require(type_of(f[1])==type_of(u),'ex_i type mismatch'); require(same(subst(f[2],f[1],u),ps[0].conclusion),'ex_i mismatch')
            h=ps[0].assumptions;c=f
        elif rule=='ex_e':
            arity(2,1); p,q=ps; f=norm(p.conclusion);require(f[0]=='ex','ex_e nonexistential');v=args[0];require(v[0]=='v' and type_of(v)==type_of(f[1]),'ex_e eigenvariable type')
            hyp=subst(f[2],f[1],v);h=union(p.assumptions,remove(q.assumptions,hyp));c=q.conclusion
            require(v not in (free_hyps(h)|set(fv(c))|set(fv(p.conclusion))), 'ex_e escaping/nonfresh eigenvariable')
        elif rule=='false_e':
            arity(1,1);require(same(ps[0].conclusion,Bot),'false_e nonfalse');proposition(args[0]);h=ps[0].assumptions;c=args[0]
        elif rule=='em':
            arity(0,1);proposition(args[0]);h=();c=Or(args[0],Not(args[0]))
        elif rule=='conv':
            arity(1,1);proposition(args[0]);require(same(ps[0].conclusion,args[0]),'invalid beta-alpha conversion');h=ps[0].assumptions;c=args[0]
        elif rule=='type_inst':
            arity(1,1); m=dict(args[0]);require('o' not in m,'cannot instantiate proposition type');require(all(isinstance(k,str) and is_type(v) for k,v in m.items()),'bad type instantiation')
            h=tuple(type_sub(a,m) for a in ps[0].assumptions);c=type_sub(ps[0].conclusion,m)
        else: raise CheckError('unknown proof rule: '+rule)
        proposition(c)
        j=Judgment(h,c); self.records.append((rule,tuple(refs),tuple(args)));self.proofs.append(j);return len(self.proofs)-1

# Compact DAG certificate: term encodings use explicit references, never code.
def freeze(x): return tuple(freeze(a) for a in x) if isinstance(x,list) else x

def save_certificate(kernel,theorems,path):
    table=[]; ids={}
    def pack(x):
        if isinstance(x,tuple):
            if x not in ids:
                y=[pack(a) for a in x];ids[x]=len(table);table.append(y)
            return {'r':ids[x]}
        return x
    records=[]
    for rule,refs,args in kernel.records:
        records.append([rule,list(refs),pack(args)])
    ends={n:[i,pack(kernel.proofs[i].conclusion)] for n,i in theorems.items()}
    with open(path,'w') as f:json.dump({'format':'classical-hol-nd-v1','terms':table,'proof':records,'theorems':ends},f,separators=(',',':'))

def load_and_check(path):
    with open(path) as f:d=json.load(f)
    require(d['format']=='classical-hol-nd-v1','format');ts=[]
    def unpack(x):
        if isinstance(x,dict):
            require(set(x)=={'r'},'term reference');i=x['r'];require(isinstance(i,int) and 0<=i<len(ts),'forward/bad term ref');return ts[i]
        require(isinstance(x,(str,int)),'bad term leaf');return x
    for row in d['terms']:ts.append(tuple(unpack(x) for x in row))
    k=Kernel()
    for rule,refs,args in d['proof']:k.add(rule,refs,unpack(args))
    for name,(i,t) in d['theorems'].items():
        require(0<=i<len(k.proofs),'bad final reference');j=k.proofs[i];require(not j.assumptions,'undischarged hypotheses in '+name);require(same(j.conclusion,unpack(t)),'final statement mismatch')
        print('VERIFIED',name,'node',i)
    print('Checked',len(k.proofs),'inference steps. Logical axiom: excluded middle.')
    return k,d
if __name__=='__main__':
    import sys
    load_and_check(sys.argv[1])
