#!/usr/bin/env python3
from __future__ import annotations
import argparse, ctypes, json, math, time
from pathlib import Path
LIBZ3='/usr/lib/x86_64-linux-gnu/libz3.so.4'

def A(xs):
    xs=list(xs)
    return 'true' if not xs else xs[0] if len(xs)==1 else '(and '+' '.join(xs)+')'
def O(xs):
    xs=list(xs)
    return 'false' if not xs else xs[0] if len(xs)==1 else '(or '+' '.join(xs)+')'
def N(x): return f'(not {x})'
def Imp(x,y): return f'(=> {x} {y})'

def bvconst(v,w): return f'(_ bv{v} {w})'
def bvor(xs):
    xs=list(xs)
    if not xs: raise ValueError('empty bvor')
    r=xs[0]
    for x in xs[1:]: r=f'(bvor {r} {x})'
    return r
def bvand(x,y): return f'(bvand {x} {y})'
def bit(row,j,w): return f'(distinct {bvand(row,bvconst(1<<j,w))} {bvconst(0,w)})'
def rowor(*rows): return bvor(rows)

class Enc:
    def __init__(self,n):
        self.n=n; self.w=n; self.rw=max(1,math.ceil(math.log2(n+1))); self.lines=[]
        self.zero=bvconst(0,n); self.all=bvconst((1<<n)-1,n)
    def declrow(self,x): self.lines.append(f'(declare-fun {x} () (_ BitVec {self.w}))')
    def declrank(self,x): self.lines.append(f'(declare-fun {x} () (_ BitVec {self.rw}))')
    def declbool(self,x): self.lines.append(f'(declare-fun {x} () Bool)')
    def ass(self,x): self.lines.append(f'(assert {x})')
    def eq(self,x,y): self.ass(f'(= {x} {y})')
    def closure(self,prefix,base_rows,refl=False):
        n=self.n
        for i in range(n):
            x=f'{prefix}_0_{i}'; self.declrow(x)
            rhs=base_rows[i]
            if refl: rhs=f'(bvor {rhs} {bvconst(1<<i,n)})'
            self.eq(x,rhs)
        for k in range(n):
            for i in range(n):
                x=f'{prefix}_{k+1}_{i}'; self.declrow(x)
                old=f'{prefix}_{k}_{i}'; kth=f'{prefix}_{k}_{k}'
                self.eq(x,f'(bvor {old} (ite {bit(old,k,n)} {kth} {self.zero}))')
        return [f'{prefix}_{n}_{i}' for i in range(n)]
    def comp(self,prefix,P,Q):
        n=self.n
        out=[]
        for i in range(n):
            x=f'{prefix}_{i}'; self.declrow(x)
            terms=[f'(ite {bit(P[i],k,n)} {Q[k]} {self.zero})' for k in range(n)]
            self.eq(x,bvor(terms)); out.append(x)
        return out
    def subset(self,L,R):
        for i in range(self.n): self.ass(f'(= (bvand {L[i]} (bvnot {R[i]})) {self.zero})')

def build(n,s0,s1,wit,h1,aesc,timeout=0,seed=0,tactic='solver',
          elast=None,elast_color=None,efirst=None,efirst_color=None,escc_mask=None):
    assert n==10 and s0==5 and s1==5 and 5<=wit<n and 0<=aesc<wit
    e=Enc(n); z=e.zero
    # relation rows
    for r in 'ABCD':
        for i in range(n): e.declrow(f'{r}_{i}')
    Arow=[f'A_{i}' for i in range(n)]; Brow=[f'B_{i}' for i in range(n)]
    Crow=[f'C_{i}' for i in range(n)]; Drow=[f'D_{i}' for i in range(n)]
    # Named union rows keep the SMT input and bit-blasted circuit compact.
    Erow=[f'E_{i}' for i in range(n)]; Frow=[f'F_{i}' for i in range(n)]
    Rrow=[f'R_{i}' for i in range(n)]; ABrow=[f'AB_{i}' for i in range(n)]
    for i in range(n):
        for x in (Erow[i],Frow[i],Rrow[i],ABrow[i]): e.declrow(x)
        e.eq(Erow[i],rowor(Brow[i],Crow[i],Drow[i]))
        e.eq(Frow[i],rowor(Crow[i],Drow[i]))
        e.eq(Rrow[i],rowor(Arow[i],Brow[i],Crow[i],Drow[i]))
        e.eq(ABrow[i],rowor(Arow[i],Brow[i]))
    # irreflexivity and A topological normalization
    full=(1<<n)-1
    for i in range(n):
        amask=sum(1<<j for j in range(i))
        e.ass(f'(= (bvand A_{i} {bvconst(full^amask,n)}) {z})')
        mask_no_diag=full^(1<<i)
        for r in 'BCD': e.ass(f'(= (bvand {r}_{i} {bvconst(full^mask_no_diag,n)}) {z})')
    # exact closures
    RS=e.closure('RS',Rrow,True)
    ES=e.closure('ES',Erow,True)
    BP=e.closure('BP',Brow,False)
    CP=e.closure('CP',Crow,False)
    ABP=e.closure('ABP',ABrow,False)
    # B,C acyclic; R strong; AB cyclic
    for i in range(n):
        e.ass(N(bit(BP[i],i,n))); e.ass(N(bit(CP[i],i,n)))
        e.eq(RS[i],e.all)
    e.ass(O(bit(ABP[i],i,n) for i in range(n)))
    # D acyclic by topological ranks
    for i in range(n): e.declrank(f'DR_{i}')
    for i in range(n):
        for j in range(n):
            if i!=j: e.ass(Imp(bit(Drow[i],j,n),f'(bvugt DR_{i} DR_{j})'))
    # Open hypotheses, using AR*=universal iff Aout under R-strong connectivity.
    EA=e.comp('EA',Erow,Arow)
    FB=e.comp('FB',Frow,Brow)
    DC=e.comp('DC',Drow,Crow)
    BES=e.comp('BES',Brow,ES)
    for i in range(n):
        aout=f'(distinct A_{i} {z})'
        rhs0=f'(ite {aout} {e.all} {Erow[i]})'
        rhs1=f'(ite {aout} {e.all} (bvor {BP[i]} {Frow[i]}))'
        rhs2=rowor(BES[i],CP[i],Drow[i])
        e.ass(f'(= (bvand {EA[i]} (bvnot {rhs0})) {z})')
        e.ass(f'(= (bvand {FB[i]} (bvnot {rhs1})) {z})')
        e.ass(f'(= (bvand {DC[i]} (bvnot {rhs2})) {z})')
    # Exact S0=S1={0,...,4} normal form.
    s0mask=(1<<s0)-1; s1mask=(1<<s1)-1
    for i in range(s0): e.eq(Arow[i],z)
    for i in range(s0,n): e.ass(f'(distinct A_{i} {z})')
    for i in range(s1):
        e.ass(f'(= (bvand {BP[i]} {bvconst(s0mask,n)}) {z})')
        e.ass(f'(distinct (bvand {Frow[i]} {bvconst(s1mask,n)}) {z})')
    for i in range(s0): e.ass(f'(distinct {Erow[i]} {z})')
    # selected pure D,C 2-cycle 0 D 1 C 0
    e.ass(bit(Drow[0],1,n)); e.ass(N(bit(Crow[0],1,n))); e.ass(bit(Crow[1],0,n))
    # F_{B!E} acyclic. E-immortality is exact on a finite domain.
    ecyc=[f'ECYC_{c}' for c in range(n)]
    eimm=[f'EIMM_{y}' for y in range(n)]
    besc=[f'BESC_{x}' for x in range(n)]
    for x in ecyc+eimm+besc: e.declbool(x)
    for c in range(n): e.ass(f'(= {ecyc[c]} {O(A([bit(Erow[c],k,n),bit(ES[k],c,n)]) for k in range(n))})')
    for y in range(n): e.ass(f'(= {eimm[y]} {O(A([bit(ES[y],c,n),ecyc[c]]) for c in range(n))})')
    for x in range(n): e.ass(f'(= {besc[x]} {O(A([bit(Brow[x],y,n),eimm[y]]) for y in range(n))})')
    for i in range(n): e.declrank(f'GR_{i}')
    for i in range(n):
        for j in range(n):
            if i!=j:
                gedge=A([bit(Frow[i],j,n),N(besc[i])])
                e.ass(Imp(gedge,f'(bvugt GR_{i} GR_{j})'))
    # L=2 forced BE* repair, least witness.
    e.ass(bit(Brow[0],wit,n)); e.ass(bit(ES[wit],0,n))
    for u in range(s0,wit): e.ass(N(A([bit(Brow[0],u,n),bit(ES[u],0,n)])))
    # H1 repair branch for 1 C 0 B wit.
    if h1=='F': e.ass(bit(Frow[1],wit,n))
    elif h1=='Bplus': e.ass(N(bit(Frow[1],wit,n))); e.ass(bit(BP[1],wit,n))
    else: raise ValueError(h1)
    # least A-successor of wit
    e.ass(bit(Arow[wit],aesc,n))
    for u in range(aesc): e.ass(N(bit(Arow[wit],u,n)))
    # Optional exact membership mask for the E-strongly-connected component of 0.
    if escc_mask is not None:
        kin=[u for u in range(n) if (escc_mask>>u)&1]
        for u in range(n):
            in_k=A([bit(ES[0],u,n),bit(ES[u],0,n)])
            e.ass(in_k if u in kin else N(in_k))
        # Redundant but propagation-friendly: a strongly connected component is
        # pairwise E-reachable, not merely mutually reachable with the root.
        for i in kin:
            for j in kin: e.ass(bit(ES[i],j,n))
    # Optional first/last path splits (least labelled witness of that kind).
    if efirst is not None:
        e.ass(bit(Erow[wit],efirst,n)); e.ass(bit(ES[efirst],0,n))
        for u in range(efirst): e.ass(N(A([bit(Erow[wit],u,n),bit(ES[u],0,n)])))
        if efirst_color:
            rel={'B':Brow,'C':Crow,'D':Drow}[efirst_color]
            e.ass(bit(rel[wit],efirst,n))
            # priority partition B < C < D
            if efirst_color in ('C','D'): e.ass(N(bit(Brow[wit],efirst,n)))
            if efirst_color=='D': e.ass(N(bit(Crow[wit],efirst,n)))
    if elast is not None:
        e.ass(bit(ES[wit],elast,n)); e.ass(bit(Erow[elast],0,n))
        for u in range(elast): e.ass(N(A([bit(ES[wit],u,n),bit(Erow[u],0,n)])))
        if elast_color:
            rel={'B':Brow,'C':Crow,'D':Drow}[elast_color]
            e.ass(bit(rel[elast],0,n))
            if elast_color in ('C','D'): e.ass(N(bit(Brow[elast],0,n)))
            if elast_color=='D': e.ass(N(bit(Crow[elast],0,n)))
    pre=[]
    if timeout: pre.append(f'(set-option :timeout {timeout})')
    pre += [f'(set-option :smt.random_seed {seed})',f'(set-option :sat.random_seed {seed})']
    if tactic=='sat': check='(check-sat-using (then simplify propagate-values solve-eqs elim-uncnstr bit-blast tseitin-cnf sat))'
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
    p=argparse.ArgumentParser(); p.add_argument('--n',type=int,default=10); p.add_argument('--s0',type=int,default=5); p.add_argument('--s1',type=int,default=5)
    p.add_argument('--witness',type=int,required=True); p.add_argument('--h1',choices=['F','Bplus'],required=True); p.add_argument('--aescape',type=int,required=True)
    p.add_argument('--efirst',type=int); p.add_argument('--efirst-color',choices=['B','C','D']); p.add_argument('--elast',type=int); p.add_argument('--elast-color',choices=['B','C','D']); p.add_argument('--escc-mask',type=lambda x:int(x,0))
    p.add_argument('--timeout-ms',type=int,default=0); p.add_argument('--seed',type=int,default=0); p.add_argument('--tactic',choices=['solver','sat','qfbv'],default='solver'); p.add_argument('--dump')
    a=p.parse_args(); t=time.time(); s=build(a.n,a.s0,a.s1,a.witness,a.h1,a.aescape,a.timeout_ms,a.seed,a.tactic,a.elast,a.elast_color,a.efirst,a.efirst_color,a.escc_mask)
    if a.dump: Path(a.dump).write_text(s)
    print(json.dumps({'event':'built','bytes':len(s),'args':vars(a),'build_s':round(time.time()-t,3)}),flush=True)
    t=time.time(); out=Z3().run(s)
    print(json.dumps({'event':'result','output':out.strip(),'solve_s':round(time.time()-t,3)}),flush=True)
if __name__=='__main__': main()
