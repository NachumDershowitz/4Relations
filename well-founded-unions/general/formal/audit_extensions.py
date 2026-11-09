"""Exact statement reconstruction independent of all proof generators.
The ordinal interface is explicit, and the carrier is not assumed finite
in any height or ordinal theorem. Height profiles are finite iteration of
H -> {x : every B-successor is in H}, starting from the empty predicate.
"""
import contextlib,io
import check_debruijn as db
from statement_syntax import *
from audit_branching import sub,nonempty,normal,norelation,representatives,cand_clear
Otype='Ord'
def rel(T):return fn(T,fn(T,o))
def ands(*xs):
    r=xs[-1]
    for x in reversed(xs[:-1]):r=conj(x,r)
    return r
def exists(vs,b):
    for v in reversed(vs):b=ex(v,b)
    return b
def irref(T,R):
    x=V(T);return fa(x,neg(ap(R,x,x)))
def transitive(T,R):
    x=V(T);y=V(T);z=V(T);return alls([x,y,z],imps([ap(R,x,y),ap(R,y,z)],ap(R,x,z)))
def trichotomy(T,R):
    x=V(T);y=V(T);return alls([x,y],disj(eq(T,x,y),disj(ap(R,x,y),ap(R,y,x))))
def wellfounded(T,R):
    H=V(fn(T,o));x=V(T);y=V(T)
    return fa(H,im(fa(x,im(fa(y,im(ap(R,x,y),ap(H,y))),ap(H,x))),fa(x,ap(H,x))))
def reverse(T,R):
    x=V(T);y=V(T);return lam(x,lam(y,ap(R,y,x)))
def relsub(A,B):
    x=V(X);y=V(X);return alls([x,y],im(ap(A,x,y),ap(B,x,y)))
def transwf(R):
    T=V(rel(X));return fa(T,imps([relsub(T,R),transitive(X,T)],wf(T)))
def domain(R,J):
    x=V(X);y=V(X);return alls([x,y],im(ap(R,x,y),conj(ap(J,x),ap(J,y))))
def serial(R,S):
    x=V(X);y=V(X);return fa(x,im(ap(S,x),ex(y,conj(ap(S,y),ap(R,x,y)))))
def localroute(R,B,S,short=False):
    x=V(X);y=V(X);z=V(X)
    out=positive(B,x,z) if short else disj(positive(B,x,z),ap(R,x,z))
    return alls([x,y,z],imps([ap(S,x),ap(S,y),ap(R,x,y),ap(B,y,z)],out))
def empty():
    x=V(X);return lam(x,false)
def nxt(B,H):
    x=V(X);y=V(X);return lam(x,fa(y,im(ap(B,x,y),ap(H,y))))
def profile(B,H):
    Q=V(fn(fn(X,o),o));U=V(fn(X,o))
    return fa(Q,imps([ap(Q,empty()),fa(U,im(ap(Q,U),ap(Q,nxt(B,U))))],ap(Q,H)))
def bounded(B,S):
    H=V(fn(X,o));return ex(H,conj(profile(B,H),sub(S,nxt(B,H))))
def pointwise(B,S):
    x=V(X);H=V(fn(X,o));return fa(x,im(ap(S,x),ex(H,conj(profile(B,H),ap(nxt(B,H),x)))))
def total(F):
    x=V(X);y=V(X);i=V(K);return lam(x,lam(y,ex(i,ap(F,i,x,y))))
def part(F,L,i,earlier=False):
    x=V(X);y=V(X);j=V(K)
    cmp=ap(L,j,i) if earlier else ap(L,i,j)
    return lam(x,lam(y,ex(j,conj(cmp,ap(F,j,x,y)))))
def det(B,R,x,z):
    u=V(X);return ex(u,conj(ap(B,x,u),star(R,u,z)))
def short_at(F,L,i):
    x=V(X);y=V(X);z=V(X);R=total(F)
    return alls([x,y,z],imps([ap(part(F,L,i),x,y),ap(F,i,y,z)],disj(det(part(F,L,i,True),R,x,z),positive(ap(F,i),x,z))))
def family_assumptions(F,L,zero,pen,last):
    i=V(K);j=V(K);R=total(F)
    least=fa(i,disj(eq(K,i,zero),ap(L,zero,i)))
    pair=conj(ap(L,pen,last),fa(i,disj(eq(K,i,last),disj(eq(K,i,pen),ap(L,i,pen)))))
    w=fa(i,wf(ap(F,i)));x=V(X);y=V(X);z=V(X)
    g0=alls([x,y,z],imps([ap(part(F,L,zero),x,y),ap(F,zero,y,z)],disj(det(ap(F,zero),R,x,z),ap(part(F,L,zero),x,z))))
    gi=alls([i,x,y,z],imps([neg(eq(K,i,zero)),ap(part(F,L,i),x,y),ap(F,i,y,z)],disj(det(part(F,L,i,True),R,x,z),disj(positive(ap(F,i),x,z),ap(part(F,L,i),x,z)))))
    return [finite_type(K),irref(K,L),transitive(K,L),trichotomy(K,L),least,pair,w,g0,gi]
def immortal(R):
    x=V(X);S=V(fn(X,o));return lam(x,ex(S,conj(ap(S,x),serial(R,S))))
def cutfamily(I,F):
    i=V(K);x=V(X);y=V(X);return lam(i,lam(x,lam(y,ands(ap(I,x),ap(F,i,x,y),ap(I,y)))))
def minima(F,I,zero):
    x=V(X);return lam(x,conj(ap(I,x),normal(ap(F,zero),x)))
def mixed(F,L,zero,pen,M):
    i=V(K);B=ap(F,i)
    return fa(i,imps([neg(eq(K,i,zero)),ap(L,i,pen)],disj(bounded(B,M),conj(short_at(F,L,i),pointwise(B,M)))))
def expected_mixed():
    F=V(fn(K,rel(X)));L=V(rel(K));zero=V(K);pen=V(K);last=V(K);R=total(F);I=immortal(R);CF=cutfamily(I,F);M=minima(CF,I,zero)
    ass=family_assumptions(F,L,zero,pen,last)+[mixed(CF,L,zero,pen,M)]
    return alls([F,L,zero,pen,last],imps(ass,wf(R)))
def expected_stage(short=False):
    R=V(rel(X));B=V(rel(X));J=V(fn(X,o));S=V(fn(X,o))
    ass=[transwf(R),relsub(B,R),domain(R,J),sub(S,J),nonempty(S),representatives(R,J,S),localroute(R,B,S,short),pointwise(B,S) if short else bounded(B,S)]
    return alls([R,B,J,S],imps(ass,cand_clear(R,B,J,S)))
def rle(L,a,b):return neg(ap(L,b,a))
def decrease(B,L,rho):
    x=V(X);y=V(X);return alls([x,y],im(ap(B,x,y),ap(L,ap(rho,y),ap(rho,x))))
def lub(B,L,rho):
    x=V(X);a=V(Otype);y=V(X)
    return alls([x,a],im(fa(y,im(ap(B,x,y),ap(L,ap(rho,y),a))),rle(L,ap(rho,x),a)))
def successor(L,b,a):
    c=V(Otype);return conj(ap(L,b,a),fa(c,im(ap(L,c,a),neg(ap(L,b,c)))))
def zerorank(L,a):
    b=V(Otype);return fa(b,neg(ap(L,b,a)))
def limitrank(L,a):
    b=V(Otype);return conj(neg(zerorank(L,a)),neg(ex(b,successor(L,b,a))))
def minimum(L,rho,S,a):
    x=V(X);return conj(ap(S,a),fa(x,im(ap(S,x),rle(L,ap(rho,a),ap(rho,x)))))
def ranklayer(rho,S,a):
    x=V(X);return lam(x,conj(ap(S,x),eq(Otype,ap(rho,x),a)))
def rankdata(F,Orel,zero,pen,L,ranks):
    i=V(K);B=ap(F,i);rho=ap(ranks,i)
    return fa(i,imps([neg(eq(K,i,zero)),ap(Orel,i,pen)],ands(short_at(F,Orel,i),decrease(B,L,rho),lub(B,L,rho))))
def obstruction(F,Orel,zero,pen,J,L,ranks):
    i=V(K);S=V(fn(X,o));a=V(X);M=minima(F,J,zero)
    return exists([i,S,a],ands(neg(eq(K,i,zero)),ap(Orel,i,pen),sub(S,M),representatives(total(F),J,S),norelation(part(F,Orel,i,True),S),minimum(L,ap(ranks,i),S,a),limitrank(L,ap(ranks,i,a))))
def zeroorsucc(F,Orel,zero,pen,J,L,ranks):
    i=V(K);x=V(X);b=V(Otype);M=minima(F,J,zero);a=ap(ranks,i,x)
    return alls([i,x],imps([neg(eq(K,i,zero)),ap(Orel,i,pen),ap(M,x)],disj(zerorank(L,a),ex(b,successor(L,b,a)))))
def expected_ordinal(termination=False):
    F=V(fn(K,rel(X)));Orel=V(rel(K));zero=V(K);pen=V(K);last=V(K);L=V(rel(Otype));ranks=V(fn(K,fn(X,Otype)))
    R=total(F);I=immortal(R);CF=cutfamily(I,F)
    ass=family_assumptions(F,Orel,zero,pen,last)+[irref(Otype,L),transitive(Otype,L),trichotomy(Otype,L),wellfounded(Otype,reverse(Otype,L)),rankdata(CF,Orel,zero,pen,L,ranks)]
    if termination:
        ass += [zeroorsucc(CF,Orel,zero,pen,I,L,ranks)];out=wf(R)
    else:
        ass += [neg(wf(R))];out=obstruction(CF,Orel,zero,pen,I,L,ranks)
    return alls([F,Orel,zero,pen,last,L,ranks],imps(ass,out))
def expected_minimum_nonsucc():
    R=V(rel(X));B=V(rel(X));J=V(fn(X,o));S=V(fn(X,o));L=V(rel(Otype));rho=V(fn(X,Otype));a=V(X);b=V(Otype)
    ass=[transwf(R),relsub(B,R),domain(R,J),representatives(R,J,S),localroute(R,B,S,True),irref(Otype,L),trichotomy(Otype,L),transitive(Otype,L),decrease(B,L,rho),lub(B,L,rho),minimum(L,rho,S,a)]
    return alls([R,B,J,S,L,rho,a],imps(ass,neg(ex(b,successor(L,b,ap(rho,a))))))
def expected_succlayer():
    R=V(rel(X));B=V(rel(X));J=V(fn(X,o));S=V(fn(X,o));L=V(rel(Otype));rho=V(fn(X,Otype));b=V(Otype);a=V(Otype);x=V(X)
    upper=fa(x,im(ap(S,x),rle(L,ap(rho,x),a)))
    ass=[transwf(R),relsub(B,R),domain(R,J),nonempty(S),representatives(R,J,S),localroute(R,B,S),trichotomy(Otype,L),transitive(Otype,L),decrease(B,L,rho),lub(B,L,rho),successor(L,b,a),upper]
    U=ranklayer(rho,S,a);Vv=lam(x,conj(ap(S,x),neg(ap(U,x))))
    out=ands(sub(Vv,S),nonempty(Vv),representatives(R,J,Vv))
    return alls([R,B,J,S,L,rho,b,a],imps(ass,out))
def expected_transwf():
    F=V(fn(K,rel(X)));C=V(fn(K,o));i=V(K)
    return alls([F,C],imps([fa(i,wf(ap(F,i))),fin(K,C),fa(i,ap(C,i))],transwf(total(F))))
def expected_acyclic():
    F=V(fn(K,rel(X)));L=V(rel(K));zero=V(K);i=V(K);x=V(X);y=V(X);z=V(X);R=total(F)
    least=fa(i,disj(eq(K,i,zero),ap(L,zero,i)))
    colors=fa(i,fa(x,neg(positive(ap(F,i),x,x))))
    g0=alls([x,y,z],imps([ap(part(F,L,zero),x,y),ap(F,zero,y,z)],disj(det(ap(F,zero),R,x,z),ap(part(F,L,zero),x,z))))
    gi=alls([i,x,y,z],imps([neg(eq(K,i,zero)),ap(part(F,L,i),x,y),ap(F,i,y,z)],disj(det(part(F,L,i,True),R,x,z),disj(positive(ap(F,i),x,z),ap(part(F,L,i),x,z)))))
    ass=[finite_type(X),finite_type(K),irref(K,L),transitive(K,L),trichotomy(K,L),least,colors,g0,gi]
    return alls([F,L,zero],imps(ass,fa(x,neg(positive(R,x,x)))))

def expected_mixed_ordinal():
    F=V(fn(K,rel(X)));Orel=V(rel(K));zero=V(K);pen=V(K);last=V(K);L=V(rel(Otype));ranks=V(fn(K,fn(X,Otype)))
    R=total(F);I=immortal(R);CF=cutfamily(I,F);M=minima(CF,I,zero)
    i=V(K);x=V(X);b=V(Otype);B=ap(CF,i);rho=ap(ranks,i);a=ap(rho,x)
    zos=fa(x,im(ap(M,x),disj(zerorank(L,a),ex(b,successor(L,b,a)))))
    data=ands(short_at(CF,Orel,i),decrease(B,L,rho),lub(B,L,rho),zos)
    mix=fa(i,imps([neg(eq(K,i,zero)),ap(Orel,i,pen)],disj(bounded(B,M),data)))
    ass=family_assumptions(F,Orel,zero,pen,last)+[irref(Otype,L),transitive(Otype,L),trichotomy(Otype,L),wellfounded(Otype,reverse(Otype,L)),mix]
    return alls([F,Orel,zero,pen,last,L,ranks],imps(ass,wf(R)))

def expected_immortal_bridge():
    R=V(rel(X));x=V(X);H=V(fn(X,o));v=V(X);w=V(X)
    ind=fa(v,im(fa(w,im(ap(R,v,w),ap(H,w))),ap(H,v)))
    acc=fa(H,im(ind,ap(H,x)))
    imm=ap(immortal(R),x)
    return alls([R,x],conj(im(imm,neg(acc)),im(neg(acc),imm)))

EXPECTED={
 'immortal_iff_nonaccessible':expected_immortal_bridge,
 'arbitrary_family_mixed_height_and_ordinal_termination':expected_mixed_ordinal,
 'family_union_transitive_subrelations_well_founded':expected_transwf,
 'uniform_height_representative_elimination':expected_stage,
 'pointwise_height_representative_elimination':lambda:expected_stage(True),
 'arbitrary_family_mixed_height_termination':expected_mixed,
 'successor_ordinal_layer_elimination':expected_succlayer,
 'minimum_layer_rank_is_not_a_successor':expected_minimum_nonsucc,
 'arbitrary_family_limit_rank_obstruction':expected_ordinal,
 'zero_or_successor_internal_ranks_imply_termination':lambda:expected_ordinal(True),
 'arbitrary_finite_acyclic_family_has_acyclic_union':expected_acyclic,
}

def run(path='proof.json'):
    with contextlib.redirect_stdout(io.StringIO()):checker,cert=db.run(path)
    for name,maker in EXPECTED.items():
        i=cert['theorems'][name][0];hyps,conclusion=checker.results[i]
        expected=db.prop(maker())
        if hyps or conclusion!=expected:raise SystemExit('EXACT EXTENSION STATEMENT AUDIT FAILED: '+name)
        if db.free(conclusion):raise SystemExit('Unbound term parameter: '+name)
        print('EXACT STATEMENT VERIFIED:',name)
    print('Eleven extension statements independently reconstructed and matched.')
    print('Heights use finite iteration; ordinal ranks have explicit order and least-upper-bound hypotheses.')
if __name__=='__main__':
    import sys
    run(sys.argv[1] if len(sys.argv)>1 else 'proof.json')
