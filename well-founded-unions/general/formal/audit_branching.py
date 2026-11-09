"""Independently reconstructed branching statements (no generator imports).
Definitions are expanded, then compared to the checked conclusions using the
independent de-Bruijn representation. In particular X is NOT assumed finite.
"""
import contextlib
import io
import check_debruijn as db
from statement_syntax import (V,o,X,K,fn,ap,fa,ex,lam,im,conj,disj,false,neg,
                          alls,imps,eq,fin,finite_type,star,positive,wf)

def sub(U,W):
    x=V(X);return fa(x,im(ap(U,x),ap(W,x)))
def finite_cover(U):
    C=V(fn(X,o));return ex(C,conj(fin(X,C),sub(U,C)))
def branching(B):
    x=V(X);y=V(X)
    return fa(x,finite_cover(lam(y,ap(B,x,y))))
def nonempty(U):
    x=V(X);return ex(x,ap(U,x))
def normal(B,x):
    y=V(X);return fa(y,neg(ap(B,x,y)))
def norelation(B,U):
    x=V(X);return fa(x,im(ap(U,x),normal(B,x)))
def representatives(R,J,U):
    z=V(X);t=V(X);x=V(X)
    return fa(z,im(ap(J,z),ex(t,conj(ap(U,t),fa(x,imps([ap(U,x),ap(R,x,z)],ap(R,x,t)))))))
def cand_clear(R,B,J,S):
    U=V(fn(X,o))
    return ex(U,conj(sub(U,S),conj(nonempty(U),conj(representatives(R,J,U),norelation(B,U)))))
def intended_branching(nochain=False,finite_domain=False,shortened=True,branch_all=False,last_shortcut=True,concise=False):
    F=V(fn(K,fn(X,fn(X,o))));L=V(fn(K,fn(K,o)));zero=V(K);pen=V(K);last=V(K)
    x=V(X);y=V(X);i=V(K);j=V(K);k=V(K)
    total=lam(x,lam(y,ex(i,ap(F,i,x,y))))
    def part(i,earlier):
        x=V(X);y=V(X);j=V(K)
        order=ap(L,j,i) if earlier else ap(L,i,j)
        return lam(x,lam(y,ex(j,conj(order,ap(F,j,x,y)))))
    def det(P,x,z):
        u=V(X);return ex(u,conj(ap(P,x,u),star(total,u,z)))
    ir=fa(i,neg(ap(L,i,i)))
    tr=alls([i,j,k],imps([ap(L,i,j),ap(L,j,k)],ap(L,i,k)))
    tri=alls([i,j],disj(eq(K,i,j),disj(ap(L,i,j),ap(L,j,i))))
    least=fa(i,disj(eq(K,i,zero),ap(L,zero,i)))
    pair=conj(ap(L,pen,last),fa(i,disj(eq(K,i,last),disj(eq(K,i,pen),ap(L,i,pen)))))
    colors=fa(i,wf(ap(F,i)))
    x=V(X);y=V(X);z=V(X)
    g0=alls([x,y,z],imps([ap(part(zero,False),x,y),ap(F,zero,y,z)],disj(det(ap(F,zero),x,z),ap(part(zero,False),x,z))))
    i=V(K);x=V(X);y=V(X);z=V(X)
    end=disj(positive(ap(F,i),x,z),ap(part(i,False),x,z)) if last_shortcut else positive(ap(F,i),x,z)
    gi=alls([i,x,y,z],imps([neg(eq(K,i,zero)),ap(part(i,False),x,y),ap(F,i,y,z)],disj(det(part(i,True),x,z),end)))
    i=V(K);x=V(X);y=V(X);z=V(X)
    short=alls([x,y,z],imps([ap(part(i,False),x,y),ap(F,i,y,z)],disj(det(part(i,True),x,z),positive(ap(F,i),x,z))))
    data=conj(branching(ap(F,i)),short) if shortened else branching(ap(F,i))
    internal=fa(i,imps([neg(eq(K,i,zero)),ap(L,i,pen)],data))
    if branch_all:
        internal=conj(internal,fa(i,branching(ap(F,i))))
    if concise:
        x=V(X);y=V(X);z=V(X)
        gi=alls([x,y,z],imps([ap(part(pen,False),x,y),ap(F,pen,y,z)],
            disj(det(part(pen,True),x,z),disj(positive(ap(F,pen),x,z),ap(part(pen,False),x,z)))))
    assumptions=[finite_type(K),ir,tr,tri,least,pair,colors,g0,gi,internal]
    if finite_domain:assumptions.insert(0,finite_type(X))
    result=wf(total)
    if nochain:
        N='N';f=V(fn(N,X));s=V(fn(N,N));a=V(N);n=V(N)
        chain=fa(n,ap(total,ap(f,n),ap(f,ap(s,n))))
        result=alls([f,s,a],neg(chain))
    return alls([F,L,zero,pen,last],imps(assumptions,result))

def intended_finite_reach():
    B=V(fn(X,fn(X,o)));x=V(X);y=V(X)
    result=fa(x,finite_cover(lam(y,star(B,x,y))))
    return fa(B,imps([wf(B),branching(B)],result))

def intended_stage():
    R=V(fn(X,fn(X,o)));B=V(fn(X,fn(X,o)));J=V(fn(X,o));S=V(fn(X,o))
    x=V(X);y=V(X);z=V(X)
    ir=fa(x,neg(ap(R,x,x)))
    br=alls([x,y],im(ap(B,x,y),ap(R,x,y)))
    domain=alls([x,y],im(ap(R,x,y),conj(ap(J,x),ap(J,y))))
    strong=alls([x,y,z],imps([ap(S,x),ap(S,y),ap(R,x,y),ap(B,y,z)],positive(B,x,z)))
    return alls([R,B,J,S],imps([ir,wf(B),br,domain,sub(S,J),nonempty(S),representatives(R,J,S),strong,branching(B)],cand_clear(R,B,J,S)))

EXPECTED={
    'finitely_branching_internal_relations_terminate':lambda:intended_branching(concise=True),
    'arbitrary_finite_family_branching_termination':intended_branching,
    'branching_termination_excludes_infinite_forward_chains':lambda:intended_branching(nochain=True),
    'well_founded_finitely_branching_finite_reachability':intended_finite_reach,
    'finitely_branching_representative_elimination':intended_stage,
}

def run(path="proof.json"):
    with contextlib.redirect_stdout(io.StringIO()):checker,cert=db.run(path)
    for name,make in EXPECTED.items():
        i=cert['theorems'][name][0];hyps,conclusion=checker.results[i]
        expected=db.prop(make())
        if hyps or conclusion!=expected:
            raise SystemExit('EXACT STATEMENT AUDIT FAILED: '+name)
        if db.free(conclusion):raise SystemExit('Unexpected free term parameter: '+name)
        print('EXACT STATEMENT VERIFIED:',name)
    print('Carrier X unrestricted; only the ordered index type K is finite.')
    print('Finite branching and shortened conditions required only at internal indices.')
    print('No branching assumption on the first or final two relations.')
    print('The final interaction retains its later-color shortcut.')
    print('No uniform bound on branching degrees, depths, or carrier size.')
    print('Reachability and finite covering sets reconstructed independently of the generator.')

if __name__=='__main__':
    import sys
    run(sys.argv[1] if len(sys.argv)>1 else 'proof.json')
