"""Independent reconstruction of the advertised, fully expanded statements.
Does not import build.py or its definitions. The de Bruijn checker first replays
all inferences; this audit then compares the main conclusions to the formulas
below, not merely to the certificate's own stored conclusion labels.
"""
import contextlib, io
import check_debruijn as db

counter=0
def V(t):
    global counter
    counter+=1;return ('v','audit'+str(counter),t)
o='o';X='X';K='K'
def fn(a,b):return ('->',a,b)
def ap(f,*xs):
    for x in xs:f=('app',f,x)
    return f

def fa(v,b):return ('all',v,b)
def ex(v,b):return ('ex',v,b)
def lam(v,b):return ('lam',v,b)
def im(a,b):return ('imp',a,b)
def conj(a,b):return ('and',a,b)
def disj(a,b):return ('or',a,b)
false=('bot',)
def neg(a):return im(a,false)
def alls(vs,b):
    for v in reversed(vs):b=fa(v,b)
    return b

def imps(ps,b):
    for p in reversed(ps):b=im(p,b)
    return b

def eq(T,x,y):
    q=V(fn(T,o));return fa(q,im(ap(q,x),ap(q,y)))
def fin(T,C):
    P=V(fn(fn(T,o),o));a=V(T);S=V(fn(T,o));x=V(T)
    empty=lam(x,false);insert=lam(x,disj(eq(T,x,a),ap(S,x)))
    return fa(P,im(ap(P,empty),im(alls([a,S],im(ap(P,S),ap(P,insert))),ap(P,C))))
def finite_type(T):
    C=V(fn(T,o));x=V(T);return ex(C,conj(fin(T,C),fa(x,ap(C,x))))
def star(P,x,y):
    H=V(fn(X,o));u=V(X);v=V(X)
    return fa(H,im(ap(H,y),im(alls([u,v],im(ap(P,u,v),im(ap(H,v),ap(H,u)))),ap(H,x))))
def positive(P,x,z):
    y=V(X);return ex(y,conj(ap(P,x,y),star(P,y,z)))
def wf(P):
    H=V(fn(X,o));x=V(X);y=V(X)
    return fa(H,im(fa(x,im(fa(y,im(ap(P,x,y),ap(H,y))),ap(H,x))),fa(x,ap(H,x))))

def intended(acyclic=False):
    F=V(fn(K,fn(X,fn(X,o))));L=V(fn(K,fn(K,o)));zero=V(K)
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
    if acyclic:
        colorhyp=fa(i,fa(x,neg(positive(ap(F,i),x,x))))
    else:colorhyp=fa(i,wf(ap(F,i)))
    x=V(X);y=V(X);z=V(X)
    g0=alls([x,y,z],imps([ap(part(zero,False),x,y),ap(F,zero,y,z)],disj(det(ap(F,zero),x,z),ap(part(zero,False),x,z))))
    i=V(K);x=V(X);y=V(X);z=V(X)
    gi=alls([i,x,y,z],imps([neg(eq(K,i,zero)),ap(part(i,False),x,y),ap(F,i,y,z)],disj(det(part(i,True),x,z),disj(positive(ap(F,i),x,z),ap(part(i,False),x,z)))))
    return alls([F,L,zero],imps([finite_type(X),finite_type(K),ir,tr,tri,least,colorhyp,g0,gi],wf(total)))

def run(path='proof.json'):
    with contextlib.redirect_stdout(io.StringIO()):checker,cert=db.run(path)
    for name,acyclic in [('arbitrary_finite_family_well_founded_union',False),('arbitrary_finite_acyclic_family_termination',True)]:
        i=cert['theorems'][name][0];h,concl=checker.results[i]
        expected=db.prop(intended(acyclic))
        if h or concl!=expected:raise SystemExit('STATEMENT AUDIT FAILED: '+name)
        if db.free(concl):raise SystemExit('Unexpected free term parameter: '+name)
        print('EXACT STATEMENT VERIFIED:',name)
    print('No bound on either domain size or number of relations.')
    print('Every earlier-relation detour and later-relation shortcut retained.')
    print('The closure, finiteness, equality and WF definitions were independently reconstructed.')

if __name__=='__main__':
    import sys
    run(sys.argv[1] if len(sys.argv)>1 else 'proof.json')
