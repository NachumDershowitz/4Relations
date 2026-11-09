#!/usr/bin/env python3
from __future__ import annotations
import argparse, ctypes, itertools, json, time
from pathlib import Path
LIBZ3='/usr/lib/x86_64-linux-gnu/libz3.so.4'

def O(xs):
    xs=list(xs)
    return 'false' if not xs else xs[0] if len(xs)==1 else '(or '+' '.join(xs)+')'
def N(x): return '(not '+x+')'
def A_(xs):
    xs=list(xs)
    return 'true' if not xs else xs[0] if len(xs)==1 else '(and '+' '.join(xs)+')'
def Imp(x,y): return '(=> '+x+' '+y+')'
def nm(r,i,j): return f'{r}_{i}_{j}'
def edge(r,i,j,n):
    if i==j or (r=='A' and not i>j): return 'false'
    return nm(r,i,j)
def U(rs,i,j,n): return O(edge(r,i,j,n) for r in rs)
def E(i,j,n): return U('BCD',i,j,n)
def F(i,j,n): return U('CD',i,j,n)
def R(i,j,n): return U('ABCD',i,j,n)
def AB(i,j,n): return U('AB',i,j,n)
def Aout(i,n): return O(edge('A',i,j,n) for j in range(n))

class Enc:
    def __init__(self,n): self.n=n; self.lines=[]; self.dec=set()
    def d(self,x):
        if x not in self.dec: self.lines.append(f'(declare-fun {x} () Bool)'); self.dec.add(x)
    def ass(self,x): self.lines.append('(assert '+x+')')
    def eq(self,x,y): self.ass('(= '+x+' '+y+')')
    def edges(self):
        for r in 'ABCD':
            for i in range(self.n):
                for j in range(self.n):
                    if i!=j and (r!='A' or i>j): self.d(nm(r,i,j))
    def closure(self,prefix,base,refl=False):
        n=self.n
        for i in range(n):
            for j in range(n):
                v=f'{prefix}_0_{i}_{j}'; self.d(v)
                self.eq(v,O([base(i,j)]+(['true'] if refl and i==j else [])))
        for k in range(n):
            for i in range(n):
                for j in range(n):
                    v=f'{prefix}_{k+1}_{i}_{j}'; self.d(v)
                    self.eq(v,O([f'{prefix}_{k}_{i}_{j}',A_([f'{prefix}_{k}_{i}_{k}',f'{prefix}_{k}_{k}_{j}'])]))
    def cl(self,p,i,j): return f'{p}_{self.n}_{i}_{j}'

def cycles(vertices,k):
    for S in itertools.combinations(vertices,k):
        root=min(S); rest=[x for x in S if x!=root]
        for P in itertools.permutations(rest):
            C=(root,)+P
            yield [(C[q],C[(q+1)%k]) for q in range(k)]

def build(n,pat,s0,s1,branch='generic',wit=None,h1='any',aesc=None,efirst=None,
          gacyc=True,shortest=True,timeout=0,seed=0,tactic='solver'):
    L=len(pat); assert 2<=L<=s1<=s0<n and pat[0].upper()=='D'
    if L>=2: assert pat[1].upper()=='C'
    e=Enc(n); e.edges()
    e.closure('RS',lambda i,j:R(i,j,n),True)
    e.closure('ES',lambda i,j:E(i,j,n),True)
    e.closure('BP',lambda i,j:edge('B',i,j,n))
    e.closure('CP',lambda i,j:edge('C',i,j,n))
    e.closure('DP',lambda i,j:edge('D',i,j,n))
    e.closure('ABP',lambda i,j:AB(i,j,n))
    for i in range(n):
        for p in ('BP','CP','DP'): e.ass(N(e.cl(p,i,i)))
    # smallest finite counterexample -> R strongly connected
    for i in range(n):
        for j in range(n): e.ass(e.cl('RS',i,j))
    e.ass(O(e.cl('ABP',i,i) for i in range(n)))
    # H0,H1 use AR*=Aout under strong connectivity
    for x in range(n):
        ao=Aout(x,n)
        for z in range(n):
            l0=O(A_([E(x,y,n),edge('A',y,z,n)]) for y in range(n))
            e.ass(Imp(l0,O([ao,E(x,z,n)])))
            l1=O(A_([F(x,y,n),edge('B',y,z,n)]) for y in range(n))
            e.ass(Imp(l1,O([ao,e.cl('BP',x,z),F(x,z,n)])))
            l2=O(A_([edge('D',x,y,n),edge('C',y,z,n)]) for y in range(n))
            be=O(A_([edge('B',x,v,n),e.cl('ES',v,z)]) for v in range(n))
            e.ass(Imp(l2,O([be,e.cl('CP',x,z),edge('D',x,z,n)])))
    # exact S0/S1 sizes in canonical initial segments
    for i in range(s0): e.ass(N(Aout(i,n)))
    for i in range(s0,n): e.ass(Aout(i,n))
    for i in range(s1):
        for j in range(s0): e.ass(N(e.cl('BP',i,j)))
        e.ass(O(F(i,j,n) for j in range(s1))) # seriality lemma on S1
    for i in range(s1,s0): e.ass(O(e.cl('BP',i,j) for j in range(s1)))
    for i in range(s0): e.ass(O(E(i,j,n) for j in range(n)))
    # selected shortest F|S1 cycle
    for i,ch in enumerate(pat.upper()):
        j=(i+1)%L
        e.ass(F(i,j,n) if ch=='X' else edge(ch,i,j,n))
    e.ass(N(edge('C',0,1,n))) # pure D first edge
    for i in range(L):
        succ=(i+1)%L
        for j in range(L):
            if j!=succ:
                e.ass(N(edge('C',i,j,n))); e.ass(N(edge('D',i,j,n)))
    if shortest:
        for k in range(2,L):
            for cyc in cycles(range(s1),k): e.ass(N(A_(F(i,j,n) for i,j in cyc)))
    # Lemma 25 consequence: F_{B!E} is acyclic
    if gacyc:
        ecyc=[O(A_([E(c,k,n),e.cl('ES',k,c)]) for k in range(n)) for c in range(n)]
        eimm=[O(A_([e.cl('ES',y,c),ecyc[c]]) for c in range(n)) for y in range(n)]
        besc=[O(A_([edge('B',x,y,n),eimm[y]]) for y in range(n)) for x in range(n)]
        e.closure('GP',lambda i,j:A_([F(i,j,n),N(besc[i])]))
        for i in range(n): e.ass(N(e.cl('GP',i,i)))
    z=0 if L==2 else 2
    if branch=='bestar':
        assert wit is not None
        e.ass(edge('B',0,wit,n)); e.ass(e.cl('ES',wit,z))
        # Partition by the least labelled BE* witness.
        for u in range(s0,wit):
            e.ass(N(A_([edge('B',0,u,n),e.cl('ES',u,z)])))
        if h1=='F': e.ass(F(L-1,wit,n))
        elif h1=='Bplus':
            e.ass(N(F(L-1,wit,n))); e.ass(e.cl('BP',L-1,wit))
        elif h1!='any': raise ValueError(h1)
        if aesc is not None:
            # Partition by the least A-successor of the witness.
            e.ass(edge('A',wit,aesc,n))
            for u in range(aesc): e.ass(N(edge('A',wit,u,n)))
        if efirst is not None:
            # Partition by the least E-successor beginning an E* path to z.
            e.ass(E(wit,efirst,n)); e.ass(e.cl('ES',efirst,z))
            for u in range(efirst):
                e.ass(N(A_([E(wit,u,n),e.cl('ES',u,z)])))
    elif branch=='cplus':
        assert wit is not None
        e.ass(edge('C',0,wit,n)); e.ass('true' if wit==z else e.cl('CP',wit,z))
    elif branch!='generic': raise ValueError(branch)
    pre=[]
    if timeout: pre.append(f'(set-option :timeout {timeout})')
    pre += [f'(set-option :smt.random_seed {seed})',f'(set-option :sat.random_seed {seed})']
    if tactic=='sat': check='(check-sat-using (then simplify propagate-values solve-eqs elim-uncnstr tseitin-cnf sat))'
    elif tactic=='qfbv': check='(check-sat-using (then simplify propagate-values solve-eqs qfbv))'
    else: check='(check-sat)'
    return '\n'.join(pre+e.lines+[check])+'\n'

class Z3:
    def __init__(self):
        L=ctypes.CDLL(LIBZ3); self.L=L
        L.Z3_mk_config.restype=ctypes.c_void_p; L.Z3_del_config.argtypes=[ctypes.c_void_p]
        L.Z3_mk_context.argtypes=[ctypes.c_void_p]; L.Z3_mk_context.restype=ctypes.c_void_p
        L.Z3_del_context.argtypes=[ctypes.c_void_p]
        L.Z3_eval_smtlib2_string.argtypes=[ctypes.c_void_p,ctypes.c_char_p]; L.Z3_eval_smtlib2_string.restype=ctypes.c_char_p
    def run(self,s):
        c=self.L.Z3_mk_config(); x=self.L.Z3_mk_context(c); self.L.Z3_del_config(c)
        try:
            r=self.L.Z3_eval_smtlib2_string(x,s.encode()); return r.decode() if r else ''
        finally: self.L.Z3_del_context(x)

def main():
    p=argparse.ArgumentParser(); p.add_argument('--n',type=int,required=True); p.add_argument('pattern')
    p.add_argument('--s0',type=int,required=True); p.add_argument('--s1',type=int,required=True)
    p.add_argument('--branch',choices=['generic','bestar','cplus'],default='generic'); p.add_argument('--witness',type=int)
    p.add_argument('--h1',choices=['any','F','Bplus'],default='any'); p.add_argument('--aescape',type=int); p.add_argument('--efirst',type=int)
    p.add_argument('--timeout-ms',type=int,default=0); p.add_argument('--seed',type=int,default=0)
    p.add_argument('--tactic',choices=['solver','sat','qfbv'],default='solver'); p.add_argument('--no-g-acyclic',action='store_true')
    p.add_argument('--no-shortest-global',action='store_true'); p.add_argument('--dump')
    a=p.parse_args(); t=time.time()
    s=build(a.n,a.pattern,a.s0,a.s1,a.branch,a.witness,a.h1,a.aescape,a.efirst,not a.no_g_acyclic,
            not a.no_shortest_global,a.timeout_ms,a.seed,a.tactic)
    if a.dump: Path(a.dump).write_text(s)
    print(json.dumps({'event':'built','n':a.n,'pattern':a.pattern,'s0':a.s0,'s1':a.s1,'branch':a.branch,
      'witness':a.witness,'h1':a.h1,'aescape':a.aescape,'efirst':a.efirst,'timeout_ms':a.timeout_ms,'seed':a.seed,
      'tactic':a.tactic,'bytes':len(s),'build_s':round(time.time()-t,3)}),flush=True)
    t=time.time(); out=Z3().run(s)
    print(json.dumps({'event':'result','output':out.strip(),'solve_s':round(time.time()-t,3)}),flush=True)
if __name__=='__main__': main()
