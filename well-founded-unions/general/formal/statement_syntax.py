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

