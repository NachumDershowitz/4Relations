"""Independent replay of classical-HOL natural-deduction certificates.

This checker does not import the generator or the named-variable kernel.
Its internal syntax uses de Bruijn indices; contexts are sets of normalized
formulas. No proof search, solver, or generated code is executed.
"""
import json
import sys
from functools import lru_cache

class Invalid(Exception): pass
def ensure(b,s):
    if not b: raise Invalid(s)

def ty(t):
    return isinstance(t,str) and bool(t) or isinstance(t,tuple) and len(t)==3 and t[0]=='->' and ty(t[1]) and ty(t[2])

def arrow(a,b):return ('->',a,b)

@lru_cache(None)
def convert(t,env=()):
    tag=t[0]
    if tag=='v':
        ensure(len(t)==3 and isinstance(t[1],str) and ty(t[2]),'invalid variable')
        for j,v in enumerate(reversed(env)):
            if t==v:return ('b',j,t[2])
        return ('f',t[1],t[2])
    if tag=='bot':ensure(len(t)==1,'bot arity');return ('bot',)
    if tag in ('lam','all','ex'):
        ensure(len(t)==3 and t[1][0]=='v','binder syntax');convert(t[1]);return (tag,t[1][2],convert(t[2],env+(t[1],)))
    ensure(tag in ('app','and','or','imp') and len(t)==3,'unknown term syntax')
    return (tag,convert(t[1],env),convert(t[2],env))

@lru_cache(None)
def typeof(t,env=()):
    tag=t[0]
    if tag=='f':ensure(ty(t[2]),'free variable type');return t[2]
    if tag=='b':
        ensure(isinstance(t[1],int) and 0<=t[1]<len(env),'unbound de Bruijn index')
        ensure(t[2]==env[-1-t[1]],'bound variable type');return t[2]
    if tag=='bot':return 'o'
    if tag in ('lam','all','ex'):
        ensure(ty(t[1]),'binder type');bt=typeof(t[2],env+(t[1],))
        if tag=='lam':return arrow(t[1],bt)
        ensure(bt=='o','quantifier over nonproposition');return 'o'
    if tag=='app':
        a=typeof(t[1],env);b=typeof(t[2],env)
        ensure(isinstance(a,tuple) and a[0]=='->' and a[1]==b,'application type');return a[2]
    ensure(tag in ('and','or','imp'),'unknown logical term')
    ensure(typeof(t[1],env)==typeof(t[2],env)=='o','connective type');return 'o'

@lru_cache(None)
def shift(t,amount,depth=0):
    if t[0]=='b':return ('b',t[1]+amount if t[1]>=depth else t[1],t[2])
    if t[0] in ('f','bot'):return t
    if t[0] in ('lam','all','ex'):return (t[0],t[1],shift(t[2],amount,depth+1))
    return (t[0],shift(t[1],amount,depth),shift(t[2],amount,depth))

@lru_cache(None)
def open_body(t,arg,depth=0):
    if t[0]=='b':
        if t[1]==depth:return shift(arg,depth)
        return ('b',t[1]-1 if t[1]>depth else t[1],t[2])
    if t[0] in ('f','bot'):return t
    if t[0] in ('lam','all','ex'):return (t[0],t[1],open_body(t[2],arg,depth+1))
    return (t[0],open_body(t[1],arg,depth),open_body(t[2],arg,depth))

@lru_cache(None)
def normal(t):
    if t[0] in ('b','f','bot'):return t
    if t[0] in ('lam','all','ex'):return (t[0],t[1],normal(t[2]))
    a,b=normal(t[1]),normal(t[2])
    if t[0]=='app' and a[0]=='lam':return normal(open_body(a[2],b))
    return (t[0],a,b)

@lru_cache(None)
def free(t):
    if t[0]=='f':return frozenset((t,))
    if t[0] in ('b','bot'):return frozenset()
    if t[0] in ('lam','all','ex'):return free(t[2])
    return free(t[1])|free(t[2])

@lru_cache(None)
def abstract(t,var,depth=0):
    if t==var:return ('b',depth,var[2])
    if t[0] in ('f','b','bot'):return t
    if t[0] in ('lam','all','ex'):return (t[0],t[1],abstract(t[2],var,depth+1))
    return (t[0],abstract(t[1],var,depth),abstract(t[2],var,depth))

def maptype(t,m):
    if isinstance(t,str):return m.get(t,t)
    return arrow(maptype(t[1],m),maptype(t[2],m))
def retype(t,m):
    if t[0] in ('b','f'):return (t[0],t[1],maptype(t[2],m))
    if t[0]=='bot':return t
    if t[0] in ('lam','all','ex'):return (t[0],maptype(t[1],m),retype(t[2],m))
    return (t[0],retype(t[1],m),retype(t[2],m))

def term(raw):
    t=convert(raw);typeof(t);return normal(t)
def prop(raw):
    t=term(raw);ensure(typeof(t)=='o','expected proposition');return t

def fvctx(h):
    f=set()
    for a in h:f.update(free(a))
    return f

class Checker:
    def __init__(self):self.results=[];self.uses_classical=False
    def step(self,r,ids,aa):
        ensure(all(isinstance(i,int) and 0<=i<len(self.results) for i in ids),'invalid/forward proof reference')
        p=[self.results[i] for i in ids]
        def count(n,m):ensure(len(p)==n and len(aa)==m,'rule arity')
        if r=='assume':
            count(0,1);c=prop(aa[0]);h=frozenset((c,))
        elif r=='imp_i':
            count(1,1);a=prop(aa[0]);h=p[0][0]-{a};c=('imp',a,p[0][1])
        elif r=='imp_e':
            count(2,0);f=p[0][1];ensure(f[0]=='imp' and f[1]==p[1][1],'modus ponens');h=p[0][0]|p[1][0];c=f[2]
        elif r=='and_i':
            count(2,0);h=p[0][0]|p[1][0];c=('and',p[0][1],p[1][1])
        elif r in ('and_l','and_r'):
            count(1,0);ensure(p[0][1][0]=='and','and projection');h=p[0][0];c=p[0][1][1 if r=='and_l' else 2]
        elif r in ('or_l','or_r'):
            count(1,1);a=prop(aa[0]);h=p[0][0];c=('or',p[0][1],a) if r=='or_l' else ('or',a,p[0][1])
        elif r=='or_e':
            count(3,0);f=p[0][1];ensure(f[0]=='or' and p[1][1]==p[2][1],'disjunction elimination');h=p[0][0]|(p[1][0]-{f[1]})|(p[2][0]-{f[2]});c=p[1][1]
        elif r=='all_i':
            count(1,1);v=term(aa[0]);ensure(v[0]=='f','all_i variable');ensure(v not in fvctx(p[0][0]),'illegal generalization');h=p[0][0];c=('all',v[2],abstract(p[0][1],v))
        elif r=='all_e':
            count(1,1);f=p[0][1];a=term(aa[0]);ensure(f[0]=='all' and f[1]==typeof(a),'universal instantiation');h=p[0][0];c=normal(open_body(f[2],a))
        elif r=='ex_i':
            count(1,2);f=prop(aa[0]);a=term(aa[1]);ensure(f[0]=='ex' and f[1]==typeof(a),'existential witness type');ensure(normal(open_body(f[2],a))==p[0][1],'existential witness statement');h=p[0][0];c=f
        elif r=='ex_e':
            count(2,1);f=p[0][1];v=term(aa[0]);ensure(v[0]=='f' and f[0]=='ex' and v[2]==f[1],'existential elimination type');a=normal(open_body(f[2],v));h=p[0][0]|(p[1][0]-{a});c=p[1][1];ensure(v not in (fvctx(h)|set(free(c))|set(free(f))),'escaping/nonfresh witness')
        elif r=='false_e':
            count(1,1);ensure(p[0][1]==('bot',),'false elimination');h=p[0][0];c=prop(aa[0])
        elif r=='em':
            count(0,1);a=prop(aa[0]);h=frozenset();c=('or',a,('imp',a,('bot',)));self.uses_classical=True
        elif r=='conv':
            count(1,1);c=prop(aa[0]);ensure(c==p[0][1],'invalid conversion');h=p[0][0]
        elif r=='type_inst':
            count(1,1);m=dict(aa[0]);ensure('o' not in m and all(isinstance(a,str) and ty(b) for a,b in m.items()),'type substitution');h=frozenset(normal(retype(a,m)) for a in p[0][0]);c=normal(retype(p[0][1],m))
        else:raise Invalid('unknown proof rule '+r)
        ensure(typeof(c)=='o','conclusion type');self.results.append((h,c))
        return h,c

def run(path):
    with open(path) as f:d=json.load(f)
    ensure(d['format']=='classical-hol-nd-v1','certificate format');table=[]
    def unpack(x):
        if isinstance(x,dict):
            ensure(set(x)=={'r'},'term reference syntax');i=x['r'];ensure(isinstance(i,int) and 0<=i<len(table),'cyclic/bad term reference');return table[i]
        ensure(isinstance(x,(str,int)),'invalid term data');return x
    for row in d['terms']:table.append(tuple(unpack(x) for x in row))
    c=Checker()
    for r,ids,a in d['proof']:c.step(r,ids,unpack(a))
    for name,(i,t) in d['theorems'].items():
        ensure(isinstance(i,int) and 0<=i<len(c.results),'invalid theorem reference');h,q=c.results[i];ensure(not h,'undischarged assumption in '+name);ensure(q==prop(unpack(t)),'statement mismatch in '+name)
        print('VERIFIED',name)
    print('Independent de-Bruijn replay:',len(c.results),'inferences;',len(d['theorems']),'closed theorems; classical logic:',c.uses_classical)
    return c,d
if __name__=='__main__':run(sys.argv[1])
