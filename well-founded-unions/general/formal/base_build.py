from kernel import *
K=Kernel(); THEOREMS={}
class P:
    def __init__(self,n): self.n=n
    @property
    def c(self):return K.proofs[self.n].conclusion
    @property
    def h(self):return K.proofs[self.n].assumptions
    def __repr__(self):return show(self.c)

def mk(r,*ps,args=()):
    try:return P(K.add(r,[p.n for p in ps],args))
    except CheckError as e:
        print('RULE FAILED',r,'ARGS',*[show(a) for a in args if isinstance(a,tuple)],'INPUT',*[show(p.c) for p in ps],sep='\n');raise

def hyp(a):return mk('assume',args=(a,))
def conv(p,a):return mk('conv',p,args=(a,))
def mp(p,q):return mk('imp_e',p,q)
def ii(a,p):return mk('imp_i',p,args=(a,))
def ai(p,q):return mk('and_i',p,q)
def al(p):return mk('and_l',p)
def ar(p):return mk('and_r',p)
def ol(p,b):return mk('or_l',p,args=(b,))
def ore(p,a):return mk('or_r',p,args=(a,))
def cases(p,f,g):
    a,b=norm(p.c)[1:];return mk('or_e',p,f(hyp(a)),g(hyp(b)))
def gen(v,p):return mk('all_i',p,args=(v,))
def spec(p,*ts):
    for t in ts:p=mk('all_e',p,args=(t,))
    return p

def ei(f,t,p):return mk('ex_i',p,args=(f,t))
def unpack(p,f):
    q=norm(p.c);require(q[0]=='ex','unpack nonex');v=fresh(type_of(q[1]),'w');qv=subst(q[2],q[1],v)
    return mk('ex_e',p,f(v,hyp(qv)),args=(v,))
def absurd(p,a=Bot):return mk('false_e',p,args=(a,))
def em(a):return mk('em',args=(a,))
def apps(f,*xs):
    for x in xs:f=App(f,x)
    return f

def alls(vs,b):
    for v in reversed(vs):b=All(v,b)
    return b

def imps(xs,b):
    for x in reversed(xs):b=Imp(x,b)
    return b

def gens(vs,p):
    for v in reversed(vs):p=gen(v,p)
    return p

def iis(xs,p):
    for x in reversed(xs):p=ii(x,p)
    return p

def apply(p,*qs):
    for q in qs:p=mp(p,q)
    return p

def lemma(n,p,variables=(),hyps=()):
    p=gens(variables,iis(hyps,p)); require(not p.h,'unclosed '+n+': '+str([show(h) for h in p.h]));THEOREMS[n]=p.n
    print('proved',n,'steps',len(K.records),flush=True);return p

def inst(p,**m):return mk('type_inst',p,args=(tuple(m.items()),))
def show(t):
    if not isinstance(t,tuple):return str(t)
    k=t[0]
    if k=='v':return t[1]
    if k=='bot':return 'False'
    if k=='app':return '('+show(t[1])+' '+show(t[2])+')'
    if k in ('all','ex','lam'):return '('+k+' '+show(t[1])+'. '+show(t[2])+')'
    return '('+show(t[1])+' '+k+' '+show(t[2])+')'

def by_contra(goal,f):
    ng=Not(goal)
    return cases(em(goal),lambda h:h,lambda n:absurd(f(n),goal))

# Definable equality, predicates, finiteness, closures and well-foundedness.
def Eq(x,y):
    p=fresh(Arr(type_of(x),O),'Q');return All(p,Imp(App(p,x),App(p,y)))
def Sub(S,T):
    x=fresh(type_of(S)[1],'x');return All(x,Imp(App(S,x),App(T,x)))
def Empty(T):
    x=fresh(T,'x');return Lam(x,Bot)
def Univ(T):
    x=fresh(T,'x');return Lam(x,Imp(Bot,Bot))
def Ins(a,S):
    x=fresh(type_of(a),'x');return Lam(x,Or(Eq(x,a),App(S,x)))
def Del(S,a):
    x=fresh(type_of(a),'x');return Lam(x,And(App(S,x),Not(Eq(x,a))))
def NE(S):
    x=fresh(type_of(S)[1],'x');return Ex(x,App(S,x))
def Fin(S):
    T=type_of(S)[1];p=fresh(Arr(Arr(T,O),O),'F');a=fresh(T,'a');s=fresh(Arr(T,O),'S')
    return All(p,Imp(App(p,Empty(T)),Imp(All(a,All(s,Imp(App(p,s),App(p,Ins(a,s))))),App(p,S))))
def WF(R):
    T=type_of(R)[1];p=fresh(Arr(T,O),'H');x=fresh(T,'x');y=fresh(T,'y')
    return All(p,Imp(All(x,Imp(All(y,Imp(apps(R,x,y),App(p,y))),App(p,x))),All(x,App(p,x))))
def Star(R,x,y):
    T=type_of(x);p=fresh(Arr(T,O),'H');u=fresh(T,'u');v=fresh(T,'v')
    return All(p,Imp(App(p,y),Imp(All(u,All(v,Imp(apps(R,u,v),Imp(App(p,v),App(p,u))))),App(p,x))))
def Plus(R,x,y):
    z=fresh(type_of(x),'z');return Ex(z,And(apps(R,x,z),Star(R,z,y)))
def No(R,x):
    y=fresh(type_of(x),'y');return All(y,Not(apps(R,x,y)))
def Rel(T):return Arr(T,Arr(T,O))

# Base equality lemmas.
X='X';x=fresh(X,'x');y=fresh(X,'y');z=fresh(X,'z');Pp=fresh(Arr(X,O),'P')
eq_refl=lemma('eq_refl',gen(Pp,ii(App(Pp,x),hyp(App(Pp,x)))),[x])
eq=Eq(x,y)
# symmetry: specialize equality at predicate lambda t. t=x
v=fresh(X,'v');pred=Lam(v,Eq(v,x))
eq_sym=lemma('eq_sym',mp(spec(hyp(eq),pred),spec(eq_refl,x)),[x,y],[eq])
def eq_transport(eqproof,pred,proof):return mp(spec(eqproof,pred),proof)

# Closure lemmata.
R=fresh(Rel(X),'R');x=fresh(X,'x');y=fresh(X,'y');z=fresh(X,'z')
H=fresh(Arr(X,O),'H');u=fresh(X,'u');v=fresh(X,'v')
step=All(u,All(v,Imp(apps(R,u,v),Imp(App(H,v),App(H,u)))))
star_refl=lemma('star_refl',gens([H],iis([App(H,x),step],hyp(App(H,x)))),[R,x])
pxy=apps(R,x,y);syz=Star(R,y,z)
step_use=spec(hyp(step),x,y)
y_proof=apply(spec(hyp(syz),H),hyp(App(H,z)),hyp(step))
star_cons=lemma('star_cons',gen(H,iis([App(H,z),step],apply(step_use,hyp(pxy),y_proof))),[R,x,y,z],[pxy,syz])
sxy=Star(R,x,y)
base=apply(spec(hyp(syz),H),hyp(App(H,z)),hyp(step))
star_trans=lemma('star_trans',gen(H,iis([App(H,z),step],apply(spec(hyp(sxy),H),base,hyp(step)))),[R,x,y,z],[sxy,syz])
plus_one=lemma('plus_one',ei(Plus(R,x,y),y,ai(hyp(pxy),spec(star_refl,R,y))),[R,x,y],[pxy])
plus_star=lemma('plus_star',unpack(hyp(Plus(R,x,y)),lambda w,h:apply(spec(star_cons,R,x,w,y),al(h),ar(h))),[R,x,y],[Plus(R,x,y)])
# prepend an edge to a plus path
plus_cons=lemma('plus_cons',ei(Plus(R,x,z),y,ai(hyp(pxy),mp(spec(plus_star,R,y,z),hyp(Plus(R,y,z))))),[R,x,y,z],[pxy,Plus(R,y,z)])
# star followed by plus
u=fresh(X,'u');v=fresh(X,'v');goalPred=Lam(u,Plus(R,u,z))
stepP=gens([u,v],iis([apps(R,u,v),Plus(R,v,z)],apply(spec(plus_cons,R,u,v,z),hyp(apps(R,u,v)),hyp(Plus(R,v,z)))))
star_plus=lemma('star_plus',apply(spec(hyp(sxy),goalPred),hyp(Plus(R,y,z)),stepP),[R,x,y,z],[sxy,Plus(R,y,z)])
plus_trans=lemma('plus_trans',apply(spec(star_plus,R,x,y,z),mp(spec(plus_star,R,x,y),hyp(Plus(R,x,y))),hyp(Plus(R,y,z))),[R,x,y,z],[Plus(R,x,y),Plus(R,y,z)])

# Well-founded relations have no positive cycles (accessibility induction).
x=fresh(X,'x');y=fresh(X,'y');hpred=Lam(x,Not(Plus(R,x,x)))
ih=All(y,Imp(apps(R,x,y),Not(Plus(R,y,y))))
loop=Plus(R,x,x)
contr=unpack(hyp(loop),lambda y,h:mp(mp(spec(hyp(ih),y),al(h)),apply(spec(star_plus,R,y,x,y),ar(h),mp(spec(plus_one,R,x,y),al(h)))))
stepH=gen(x,iis([ih,loop],contr))
wf_acyclic=lemma('wf_acyclic',apply(spec(hyp(WF(R)),hpred),stepH),[R],[WF(R)])

# Convenience builders (all invoke the checked inference constructors above).
def intro(a,f):return ii(a,f(hyp(a)))
def For(v,f):return gen(v,f(v))
def use(th,ts,hs=()):return apply(spec(th,*ts),*hs)
def refl(t):return spec(inst(eq_refl,X=type_of(t)),t)
def minformula(R,S,x):
    y=fresh(type_of(x),'y');return And(App(S,x),All(y,Imp(apps(R,x,y),Not(App(S,y)))))
def minexists(R,S):
    x=fresh(type_of(S)[1],'x');return Ex(x,minformula(R,S,x))
def sourceformula(R,S,x):
    y=fresh(type_of(x),'y');return And(App(S,x),All(y,Imp(App(S,y),Not(apps(R,y,x)))))
def sourceexists(R,S):
    x=fresh(type_of(S)[1],'x');return Ex(x,sourceformula(R,S,x))

# Accessibility induction implies the usual minimal-element characterization.
R=fresh(Rel(X),'R');S=fresh(Arr(X,O),'S');x=fresh(X,'x');y=fresh(X,'y')
mex=minexists(R,S);Pmin=Lam(x,Imp(App(S,x),mex));ih=All(y,Imp(apps(R,x,y),Imp(App(S,y),mex)))
succ=Ex(y,And(apps(R,x,y),App(S,y)))
def min_step(ihp):
    def atx(sx):
        def yes(h):return unpack(h,lambda y,q:apply(spec(ihp,y),al(q),ar(q)))
        def no(h):
            yy=fresh(X,'y')
            m=For(yy,lambda yy:intro(apps(R,x,yy),lambda edge:intro(App(S,yy),lambda sy:mp(h,ei(succ,yy,ai(edge,sy))))))
            return ei(mex,x,ai(sx,m))
        return cases(em(succ),yes,no)
    return intro(App(S,x),atx)
minstep=For(x,lambda x:intro(ih,min_step))
wf_minimum=lemma('wf_minimum',unpack(hyp(NE(S)),lambda a,sa:mp(spec(apply(spec(hyp(WF(R)),Pmin),minstep),a),sa)),[R,S],[WF(R),NE(S)])

# Well-foundedness cannot coexist with a nonempty serial subset.
x=fresh(X,'x');y=fresh(X,'y');serial=All(x,Imp(App(S,x),Ex(y,And(App(S,y),apps(R,x,y)))))
def min_conflict(x,h):
    return unpack(mp(spec(hyp(serial),x),al(h)),lambda y,q:apply(spec(ar(h),y),ar(q),al(q)))
wf_no_serial=lemma('wf_no_serial',unpack(use(wf_minimum,[R,S],[hyp(WF(R)),hyp(NE(S))]),min_conflict),[R,S],[WF(R),NE(S),serial])

# Monotonicity of well-foundedness.
Q=fresh(Rel(X),'Q');x=fresh(X,'x');y=fresh(X,'y');H=fresh(Arr(X,O),'H')
sub=All(x,All(y,Imp(apps(R,x,y),apps(Q,x,y))))
stepR=All(x,Imp(All(y,Imp(apps(R,x,y),App(H,y))),App(H,x)))
stepQ=For(x,lambda x:intro(All(y,Imp(apps(Q,x,y),App(H,y))),lambda ih:
    mp(spec(hyp(stepR),x),For(y,lambda y:intro(apps(R,x,y),lambda e:mp(spec(ih,y),mp(spec(hyp(sub),x,y),e)))))))
wf_mono=lemma('wf_mono',For(H,lambda H:intro(stepR,lambda sr:mp(spec(hyp(WF(Q)),H),stepQ))),[R,Q],[sub,WF(Q)])

# Every point has a normal form under a well-founded relation.
x=fresh(X,'x');t=fresh(X,'t');y=fresh(X,'y')
def nf(x):
    t=fresh(X,'t');return Ex(t,And(Star(R,x,t),No(R,t)))
NFP=Lam(x,nf(x));ih=All(y,Imp(apps(R,x,y),nf(y)));succ=Ex(y,apps(R,x,y))
def nf_step(h):
    def yes(e):
        return unpack(e,lambda y,xy:unpack(mp(spec(h,y),xy),lambda t,p:ei(nf(x),t,ai(use(star_cons,[R,x,y,t],[xy,al(p)]),ar(p)))))
    def no(e):
        yy=fresh(X,'y');normal=For(yy,lambda yy:intro(apps(R,x,yy),lambda q:mp(e,ei(succ,yy,q))))
        return ei(nf(x),x,ai(spec(star_refl,R,x),normal))
    return cases(em(succ),yes,no)
nfstep=For(x,lambda x:intro(ih,nf_step))
wf_normal=lemma('wf_normal',mp(spec(hyp(WF(R)),NFP),nfstep),[R],[WF(R)])

# The reflexive-transitive closure has its expected one-step decomposition.
x=fresh(X,'x');y=fresh(X,'y');u=fresh(X,'u');v=fresh(X,'v')
Split=Lam(u,Or(Eq(u,y),Plus(R,u,y)))
base=ol(refl(y),Plus(R,y,y))
def splitstep(e):
    def eqcase(eq):
        zz=fresh(X,'z');tail=eq_transport(eq,Lam(zz,Star(R,v,zz)),spec(star_refl,R,v))
        return ore(ei(Plus(R,u,y),v,ai(e,tail)),Eq(u,y))
    return intro(Or(Eq(v,y),Plus(R,v,y)),lambda h:cases(h,eqcase,lambda p:ore(use(plus_cons,[R,u,v,y],[e,p]),Eq(u,y))))
ss=gens([u,v],intro(apps(R,u,v),splitstep))
star_split=lemma('star_split',apply(spec(hyp(Star(R,x,y)),Split),base,ss),[R,x,y],[Star(R,x,y)])

# Finiteness is defined by the induction principle for empty sets and insertion.
# The following source lemma is proved by that principle, not assumed.
T=fresh(Rel(X),'T');U=fresh(Arr(X,O),'U');Vv=fresh(Arr(X,O),'V')
x=fresh(X,'x');y=fresh(X,'y');z=fresh(X,'z')
IR=All(x,Not(apps(T,x,x)))
TR=alls([x,y,z],imps([apps(T,x,y),apps(T,y,z)],apps(T,x,z)))
def srcprop(U):
    vv=fresh(Arr(X,O),'V');return All(vv,imps([Sub(vv,U),NE(vv)],sourceexists(T,vv)))

# Base of finite-source induction.
v=fresh(Arr(X,O),'V');xx=fresh(X,'x')
base=For(v,lambda v:intro(Sub(v,Empty(X)),lambda h:intro(NE(v),lambda ne:
    unpack(ne,lambda x,vx:absurd(mp(spec(h,x),vx),sourceexists(T,v))))))

a=fresh(X,'a');L=fresh(Arr(X,O),'L');v=fresh(Arr(X,O),'V')
ih=srcprop(L)
def source_step(ihp):
    def onV(cover):
        def onNE(ne):
            def without(na):
                xx=fresh(X,'x');w=fresh(X,'w')
                subl=For(xx,lambda xx:intro(App(v,xx),lambda vx:cases(mp(spec(cover,xx),vx),
                    lambda eq:absurd(mp(na,eq_transport(eq,Lam(w,App(v,w)),vx)),App(L,xx)),lambda lx:lx)))
                return apply(spec(ihp,v),subl,ne)
            def witha(va):
                xx=fresh(X,'x');tail=Lam(xx,And(App(L,xx),App(v,xx)))
                def none(nt):
                    yy=fresh(X,'y');w=fresh(X,'w')
                    def miny(vy):
                        def edge(ya):
                            return cases(mp(spec(cover,yy),vy),
                                lambda eq:mp(spec(hyp(IR),a),eq_transport(eq,Lam(w,apps(T,w,a)),ya)),
                                lambda ly:mp(nt,ei(NE(tail),yy,ai(ly,vy))))
                        return intro(apps(T,yy,a),edge)
                    return ei(sourceexists(T,v),a,ai(va,For(yy,lambda yy:intro(App(v,yy),miny))))
                def has(nt):
                    xx=fresh(X,'x')
                    subl=For(xx,lambda xx:intro(App(tail,xx),lambda h:al(h)))
                    chosen=apply(spec(ihp,tail),subl,nt)
                    def atz(z,h):
                        vz=ar(al(h));minimum=ar(h);yy=fresh(X,'y');w=fresh(X,'w')
                        def yes(az):
                            def miny(vy):
                                def edge(ya):
                                    return cases(mp(spec(cover,yy),vy),
                                        lambda eq:mp(spec(hyp(IR),a),eq_transport(eq,Lam(w,apps(T,w,a)),ya)),
                                        lambda ly:mp(mp(spec(minimum,yy),ai(ly,vy)),apply(spec(hyp(TR),yy,a,z),ya,az)))
                                return intro(apps(T,yy,a),edge)
                            return ei(sourceexists(T,v),a,ai(va,For(yy,lambda yy:intro(App(v,yy),miny))))
                        def no(naz):
                            def miny(vy):
                                def edge(yz):
                                    return cases(mp(spec(cover,yy),vy),
                                        lambda eq:mp(naz,eq_transport(eq,Lam(w,apps(T,w,z)),yz)),
                                        lambda ly:mp(mp(spec(minimum,yy),ai(ly,vy)),yz))
                                return intro(apps(T,yy,z),edge)
                            return ei(sourceexists(T,v),z,ai(vz,For(yy,lambda yy:intro(App(v,yy),miny))))
                        return cases(em(apps(T,a,z)),yes,no)
                    return unpack(chosen,atz)
                return cases(em(NE(tail)),has,none)
            return cases(em(App(v,a)),witha,without)
        return intro(NE(v),onNE)
    return For(v,lambda v:intro(Sub(v,Ins(a,L)),onV))
step=gens([a,L],intro(ih,source_step))
q=fresh(Arr(X,O),'U');Qsrc=Lam(q,srcprop(q))
finite_source=lemma('finite_source',apply(spec(hyp(Fin(U)),Qsrc),base,step),[T,U],[IR,TR,Fin(U)])

# Ordinary subset operations.
S=fresh(Arr(X,O),'S');T=fresh(Arr(X,O),'T');U=fresh(Arr(X,O),'U');x=fresh(X,'x')
subset_refl=lemma('subset_refl',For(x,lambda x:intro(App(S,x),lambda h:h)),[S])
subset_trans=lemma('subset_trans',For(x,lambda x:intro(App(S,x),lambda h:mp(spec(hyp(Sub(T,U)),x),mp(spec(hyp(Sub(S,T)),x),h)))),[S,T,U],[Sub(S,T),Sub(T,U)])
def Eqv(S,T):return And(Sub(S,T),Sub(T,S))
def minimal(G,S):
    v=fresh(type_of(S),'V');return And(App(G,S),All(v,imps([Sub(v,S),App(G,v)],Sub(S,v))))
def minimal_ex(G,U):
    s=fresh(type_of(U),'S');return Ex(s,And(Sub(s,U),minimal(G,s)))
def candidate_ex(G,U):
    s=fresh(type_of(U),'S');return Ex(s,And(Sub(s,U),App(G,s)))
def minprop(U):
    g=fresh(Arr(type_of(U),O),'G');return All(g,Imp(candidate_ex(g,U),minimal_ex(g,U)))

def eqv_refl(S):
    p=spec(subset_refl,S);return ai(p,p)
def reverse_eq(eq,x,y):return mp(spec(eq_sym,x,y),eq)

G=fresh(Arr(Arr(X,O),O),'G');empty=Empty(X)
def minbase_case(S,h):
    cov=al(h);gs=ar(h);Vv=fresh(Arr(X,O),'V');x=fresh(X,'x')
    mn=For(Vv,lambda Vv:intro(Sub(Vv,S),lambda unused:intro(App(G,Vv),lambda unused2:
        For(x,lambda x:intro(App(S,x),lambda sx:absurd(mp(spec(cov,x),sx),App(Vv,x)))))))
    return ei(minimal_ex(G,empty),S,ai(cov,ai(gs,mn)))
minbase=For(G,lambda G:intro(candidate_ex(G,empty),lambda h:unpack(h,minbase_case)))

a=fresh(X,'a');L=fresh(Arr(X,O),'L');G=fresh(Arr(Arr(X,O),O),'G');cover=Ins(a,L)
def minstep_do(ihp):
    def forG(cand):
        s=fresh(Arr(X,O),'S');avo=Ex(s,And(Sub(s,cover),And(App(G,s),Not(App(s,a)))))
        def yes(avo_p):
            def chosen(S,h):
                cov=al(h);gs=al(ar(h));nsa=ar(ar(h));x=fresh(X,'x');w=fresh(X,'w')
                subl=For(x,lambda x:intro(App(S,x),lambda sx:cases(mp(spec(cov,x),sx),
                    lambda eq:absurd(mp(nsa,eq_transport(eq,Lam(w,App(S,w)),sx)),App(L,x)),lambda lx:lx)))
                got=mp(spec(ihp,G),ei(candidate_ex(G,L),S,ai(subl,gs)))
                def result(T,h):
                    subtl=al(h);mn=ar(h);xx=fresh(X,'x')
                    subtc=For(xx,lambda xx:intro(App(T,xx),lambda tx:ore(mp(spec(subtl,xx),tx),Eq(xx,a))))
                    return ei(minimal_ex(G,cover),T,ai(subtc,mn))
                return unpack(got,result)
            return unpack(avo_p,chosen)
        def no(navo):
            # Every admissible set contains a.
            def must_a(S,cov,gs):
                return by_contra(App(S,a),lambda nsa:mp(navo,ei(avo,S,ai(cov,ai(gs,nsa)))))
            w=fresh(Arr(X,O),'W');ss=fresh(Arr(X,O),'S')
            H=Lam(w,Ex(ss,And(Sub(ss,cover),And(App(G,ss),Eqv(w,Del(ss,a))))))
            def del_sub_l(S,cov):
                xx=fresh(X,'x');D=Del(S,a)
                return For(xx,lambda xx:intro(App(D,xx),lambda dx:cases(mp(spec(cov,xx),al(dx)),
                    lambda eq:absurd(mp(ar(dx),eq),App(L,xx)),lambda lx:lx)))
            def make_h(S,cov,gs):
                W=Del(S,a)
                return ei(norm(App(H,W)),S,ai(cov,ai(gs,eqv_refl(W))))
            def makecandidate(S,h):
                cov=al(h);gs=ar(h);W=Del(S,a)
                return ei(candidate_ex(H,L),W,ai(del_sub_l(S,cov),make_h(S,cov,gs)))
            h_candidate=unpack(cand,makecandidate)
            got=mp(spec(ihp,H),h_candidate)
            def withW(W,h):
                hw=al(ar(h));wmin=ar(ar(h))
                def withS(S,hs):
                    cov=al(hs);gs=al(ar(hs));equiv=ar(ar(hs))
                    VV=fresh(Arr(X,O),'V')
                    def onV(vs):
                        def onGV(gv):
                            vcover=apply(spec(subset_trans,VV,S,cover),vs,cov)
                            va=must_a(VV,vcover,gv);DV=Del(VV,a)
                            xx=fresh(X,'x')
                            dvw=For(xx,lambda xx:intro(App(DV,xx),lambda d:
                                mp(spec(ar(equiv),xx),ai(mp(spec(vs,xx),al(d)),ar(d)))))
                            hdv=make_h(VV,vcover,gv)
                            wdv=apply(spec(wmin,DV),dvw,hdv)
                            xx=fresh(X,'x');ww=fresh(X,'w')
                            def onSX(sx):
                                def samea(eq):return eq_transport(reverse_eq(eq,xx,a),Lam(ww,App(VV,ww)),va)
                                def diffa(neq):
                                    wx=mp(spec(ar(equiv),xx),ai(sx,neq))
                                    return al(mp(spec(wdv,xx),wx))
                                return cases(em(Eq(xx,a)),samea,diffa)
                            return For(xx,lambda xx:intro(App(S,xx),onSX))
                        return intro(App(G,VV),onGV)
                    m=For(VV,lambda VV:intro(Sub(VV,S),onV))
                    return ei(minimal_ex(G,cover),S,ai(cov,ai(gs,m)))
                return unpack(hw,withS)
            return unpack(got,withW)
        return cases(em(avo),yes,no)
    return For(G,lambda G:intro(candidate_ex(G,cover),forG))
minstep=gens([a,L],intro(minprop(L),minstep_do))
U=fresh(Arr(X,O),'U');q=fresh(Arr(X,O),'U')
finite_minimal_subset=lemma('finite_minimal_subset',apply(spec(hyp(Fin(U)),Lam(q,minprop(q))),minbase,minstep),[U],[Fin(U)])

# Two closure transport principles.
R=fresh(Rel(X),'R');Q=fresh(Rel(X),'Q');J=fresh(Arr(X,O),'J')
x=fresh(X,'x');y=fresh(X,'y');u=fresh(X,'u');v=fresh(X,'v')
forward=alls([u,v],imps([apps(R,u,v),App(J,u)],App(J,v)))
pred=Lam(u,Imp(App(J,u),App(J,y)))
base=intro(App(J,y),lambda h:h)
step=gens([u,v],intro(apps(R,u,v),lambda e:intro(Imp(App(J,v),App(J,y)),lambda ih:intro(App(J,u),lambda ju:mp(ih,apply(spec(hyp(forward),u,v),e,ju))))))
star_forward=lemma('star_forward',apply(spec(hyp(Star(R,x,y)),pred),base,step,hyp(App(J,x))),[R,J,x,y],[forward,Star(R,x,y),App(J,x)])
inc=alls([u,v],Imp(apps(R,u,v),apps(Q,u,v)))
pred=Lam(u,Star(Q,u,y))
step=gens([u,v],intro(apps(R,u,v),lambda e:intro(Star(Q,v,y),lambda s:use(star_cons,[Q,u,v,y],[mp(spec(hyp(inc),u,v),e),s]))))
star_mono=lemma('star_mono',apply(spec(hyp(Star(R,x,y)),pred),spec(star_refl,Q,y),step),[R,Q,x,y],[inc,Star(R,x,y)])

# General representative deletion; only elementary logic is needed here.
def Rep(R,J,S):
    ty=type_of(J)[1];z=fresh(ty,'z');t=fresh(ty,'t');x=fresh(ty,'x')
    return All(z,Imp(App(J,z),Ex(t,And(App(S,t),All(x,imps([App(S,x),apps(R,x,z)],apps(R,x,t)))))))

def rep_target(R,J,S,z):
    q=norm(Rep(R,J,S));return norm(subst(q[2][2],q[1],z))

def domain(R,J):
    x=fresh(type_of(J)[1],'x');y=fresh(type_of(J)[1],'y')
    return alls([x,y],Imp(apps(R,x,y),And(App(J,x),App(J,y))))
def serial_target(R,J,x):
    q=norm(serial(R,J));return norm(subst(q[2][2],q[1],x))

def serial(R,J):
    x=fresh(type_of(J)[1],'x');y=fresh(type_of(J)[1],'y')
    return All(x,Imp(App(J,x),Ex(y,And(App(J,y),apps(R,x,y)))))

R=fresh(Rel(X),'R');B=fresh(Rel(X),'B');J=fresh(Arr(X,O),'J');S=fresh(Arr(X,O),'S');z=fresh(X,'z');t=fresh(X,'t')
x=fresh(X,'x');y=fresh(X,'y')
selected=Ex(y,And(App(S,y),apps(B,y,z)))
repz=All(x,imps([App(S,x),apps(R,x,z)],apps(R,x,t)))
transfer=alls([x,y],imps([App(S,x),App(S,y),apps(B,y,z),apps(R,x,y)],apps(R,x,t)))
# We use the surviving representative as an explicit witness of nonemptiness.
notbt=Not(apps(B,t,z));Sp=Lam(x,And(App(S,x),Not(apps(B,x,z))))
def foldrep(v,jv):
    old=mp(spec(hyp(Rep(R,J,S)),v),jv)
    def withu(u,hu):
        su=al(hu);oldr=ar(hu);xx=fresh(X,'x')
        def yes(buz):
            newr=For(xx,lambda xx:intro(App(Sp,xx),lambda h:intro(apps(R,xx,v),lambda e:
                apply(spec(hyp(transfer),xx,u),al(h),su,buz,apply(spec(oldr,xx),al(h),e)))))
            return ei(rep_target(R,J,Sp,v),t,ai(ai(hyp(App(S,t)),hyp(notbt)),newr))
        def no(nbuz):
            newr=For(xx,lambda xx:intro(App(Sp,xx),lambda h:intro(apps(R,xx,v),lambda e:apply(spec(oldr,xx),al(h),e))))
            target=rep_target(R,J,Sp,v)
            return ei(target,u,ai(ai(su,nbuz),newr))
        return cases(em(apps(B,u,z)),yes,no)
    return unpack(old,withu)
v=fresh(X,'v')
fold_rep=lemma('fold_representatives',For(v,lambda v:intro(App(J,v),lambda jv:foldrep(v,jv))),[R,B,J,S,z,t],[Rep(R,J,S),App(S,t),notbt,transfer])

# Family notation. All index types are arbitrary finite linearly ordered types.
Idx='K';FamTy=Arr(Idx,Rel(X))
def Total(F):
    x=fresh(X,'x');y=fresh(X,'y');i=fresh(Idx,'i')
    return Lam(x,Lam(y,Ex(i,apps(F,i,x,y))))
def Part(F,O,i,earlier=False):
    x=fresh(X,'x');y=fresh(X,'y');j=fresh(Idx,'j')
    condition=apps(O,j,i) if earlier else apps(O,i,j)
    return Lam(x,Lam(y,Ex(j,And(condition,apps(F,j,x,y)))))
def Detour(B,R,x,z):
    y=fresh(X,'y');return Ex(y,And(apps(B,x,y),Star(R,y,z)))
def Gzero(F,O,zero):
    x=fresh(X,'x');y=fresh(X,'y');z=fresh(X,'z');R=Total(F);A=App(F,zero);T=Part(F,O,zero)
    return alls([x,y,z],imps([apps(T,x,y),apps(A,y,z)],Or(Detour(A,R,x,z),apps(T,x,z))))
def Gothers(F,O,zero):
    i=fresh(Idx,'i');x=fresh(X,'x');y=fresh(X,'y');z=fresh(X,'z');R=Total(F);A=App(F,i);T=Part(F,O,i);P=Part(F,O,i,True)
    return alls([i,x,y,z],imps([Not(Eq(i,zero)),apps(T,x,y),apps(A,y,z)],Or(Detour(P,R,x,z),Or(Plus(A,x,z),apps(T,x,z)))))
def WFcolors(F):
    i=fresh(Idx,'i');return All(i,WF(App(F,i)))
def least(O,zero):
    i=fresh(Idx,'i');return All(i,Or(Eq(i,zero),apps(O,zero,i)))
def tri(O):
    i=fresh(Idx,'i');j=fresh(Idx,'j');return alls([i,j],Or(Eq(i,j),Or(apps(O,i,j),apps(O,j,i))))
def irrefl(R):
    ty=type_of(R)[1];x=fresh(ty,'x');return All(x,Not(apps(R,x,x)))
def trans(R):
    ty=type_of(R)[1];x=fresh(ty,'x');y=fresh(ty,'y');z=fresh(ty,'z');return alls([x,y,z],imps([apps(R,x,y),apps(R,y,z)],apps(R,x,z)))

F=fresh(FamTy,'F');Orel=fresh(Rel(Idx),'order');zero=fresh(Idx,'zero');R=Total(F);A=App(F,zero)
x=fresh(X,'x');y=fresh(X,'y');i=fresh(Idx,'i')
# Inclusions and irreflexivity of the union.
color_total=lemma('color_total',ei(norm(apps(R,x,y)),i,hyp(apps(F,i,x,y))),[F,i,x,y],[apps(F,i,x,y)])
part=Part(F,Orel,i)
def part_to_total(j,h):return use(color_total,[F,j,x,y],[ar(h)])
tail_total=lemma('tail_total',unpack(hyp(apps(part,x,y)),part_to_total),[F,Orel,i,x,y],[apps(part,x,y)])
partE=Part(F,Orel,i,True)
earlier_total=lemma('earlier_total',unpack(hyp(apps(partE,x,y)),part_to_total),[F,Orel,i,x,y],[apps(partE,x,y)])
union_irrefl=lemma('union_irrefl',For(x,lambda x:intro(apps(R,x,x),lambda h:unpack(h,lambda i,e:
    mp(spec(mp(spec(wf_acyclic,App(F,i)),spec(hyp(WFcolors(F)),i)),x),use(plus_one,[App(F,i),x,x],[e]))))),[F],[WFcolors(F)])

# At an A-normal source, every union edge is a later-color edge.
x=fresh(X,'x');y=fresh(X,'y');T0=Part(F,Orel,zero)
def classify(j,e):
    def equal(eq):
        k=fresh(Idx,'k');axy=eq_transport(eq,Lam(k,apps(F,k,x,y)),e)
        return absurd(mp(spec(hyp(No(A,x)),y),axy),apps(T0,x,y))
    def later(h):return ei(norm(apps(T0,x,y)),j,ai(h,e))
    return cases(spec(hyp(least(Orel,zero)),j),equal,later)
normal_tail=lemma('normal_tail',unpack(hyp(apps(R,x,y)),classify),[F,Orel,zero,x,y],[least(Orel,zero),No(A,x),apps(R,x,y)])

# Construction of the initial representative set.
J=fresh(Arr(X,O),'J');x=fresh(X,'x');M=Lam(x,And(App(J,x),No(A,x)))
z=fresh(X,'z');t=fresh(X,'t');u=fresh(X,'u');v=fresh(X,'v')
Dom=domain(R,J)
a_forward=gens([u,v],intro(apps(A,u,v),lambda e:intro(App(J,u),lambda ju:ar(mp(spec(hyp(Dom),u,v),use(color_total,[F,zero,u,v],[e]))))))

def initial_at(z,jz):
    got=spec(mp(spec(wf_normal,A),spec(hyp(WFcolors(F)),zero)),z)
    def witht(t,h):
        path=al(h);nt=ar(h)
        jt=use(star_forward,[A,J,z,t],[a_forward,path,jz])
        xx=fresh(X,'x');vv=fresh(X,'v');uu=fresh(X,'u')
        def atx(mx):
            nx=ar(mx)
            def edge(rxz):
                txz=use(normal_tail,[F,Orel,zero,xx,z],[hyp(least(Orel,zero)),nx,rxz])
                pred=Lam(vv,apps(T0,xx,vv))
                def along(e):
                    def prior(txx):
                        g=apply(spec(hyp(Gzero(F,Orel,zero)),xx,uu,vv),txx,e)
                        return cases(g,lambda d:unpack(d,lambda w,dw:absurd(mp(spec(nx,w),al(dw)),apps(T0,xx,vv))),lambda f:f)
                    return intro(apps(T0,xx,uu),prior)
                fw=gens([uu,vv],intro(apps(A,uu,vv),along))
                txt=use(star_forward,[A,pred,z,t],[fw,path,txz])
                return use(tail_total,[F,Orel,zero,xx,t],[txt])
            return intro(apps(R,xx,z),edge)
        rp=For(xx,lambda xx:intro(App(M,xx),atx))
        target=rep_target(R,J,M,z)
        return ei(target,t,ai(ai(jt,nt),rp))
    return unpack(got,witht)
init_rep=lemma('initial_representatives',For(z,lambda z:intro(App(J,z),lambda h:initial_at(z,h))),[F,Orel,zero,J],[WFcolors(F),least(Orel,zero),Gzero(F,Orel,zero),Dom])
# Nonemptiness of M follows from a normal form of any J point.
def m_nonempty(z,jz):
    got=spec(mp(spec(wf_normal,A),spec(hyp(WFcolors(F)),zero)),z)
    return unpack(got,lambda t,h:ei(NE(M),t,ai(use(star_forward,[A,J,z,t],[a_forward,al(h),jz]),ar(h))))
init_nonempty=lemma('initial_nonempty',unpack(hyp(NE(J)),m_nonempty),[F,zero,J],[WFcolors(F),Dom,NE(J)])


# The full finite serial-domain contradiction for an arbitrary finite family.
F=fresh(FamTy,'F');Orel=fresh(Rel(Idx),'order');zero=fresh(Idx,'zero');J=fresh(Arr(X,O),'J')
CX=fresh(Arr(X,O),'coverX');CK=fresh(Arr(Idx,O),'coverK');R=Total(F);A=App(F,zero)
x=fresh(X,'x');M=Lam(x,And(App(J,x),No(A,x)))
ki=fresh(Idx,'i');allK=All(ki,App(CK,ki))
ass=[Fin(CX),Sub(J,CX),Fin(CK),allK,irrefl(Orel),trans(Orel),tri(Orel),least(Orel,zero),WFcolors(F),Gzero(F,Orel,zero),Gothers(F,Orel,zero),domain(R,J),NE(J),serial(R,J)]
HfinX,HcoverX,HfinK,HallK,Hoi,Hot,Hotri,Hleast,Hwf,Hg0,Hg,HD,Hne,HS=map(hyp,ass)
ss=fresh(Arr(X,O),'S');Good=Lam(ss,And(NE(ss),And(Sub(ss,M),Rep(R,J,ss))))
mx=fresh(X,'x')
mcov=For(mx,lambda mx:intro(App(M,mx),lambda h:mp(spec(HcoverX,mx),al(h))))
mne=use(init_nonempty,[F,zero,J],[Hwf,HD,Hne])
mrep=use(init_rep,[F,Orel,zero,J],[Hwf,Hleast,Hg0,HD])
goodM=ai(mne,ai(spec(subset_refl,M),mrep))
candidate=ei(candidate_ex(Good,CX),M,ai(mcov,goodM))
minimalS=mp(spec(mp(spec(finite_minimal_subset,CX),HfinX),Good),candidate)


def core_with_S(S,hS):
    good=al(ar(hS));Smin=ar(ar(hS));NS=al(good);SM=al(ar(good));rep=ar(ar(good))
    def sJ(x,sx):return al(mp(spec(SM,x),sx))
    def sNo(x,sx):return ar(mp(spec(SM,x),sx))
    def active(i):
        x=fresh(X,'x');z=fresh(X,'z');return Ex(x,Ex(z,And(App(S,x),apps(F,i,x,z))))
    ii=fresh(Idx,'i');Active=Lam(ii,active(ii))
    # Build the two existential witnesses of an active color.
    def active_proof(i,x,z,sx,e):
        goal=active(i);inner=norm(subst(goal[2],goal[1],x))
        return ei(goal,x,ei(inner,z,ai(sx,e)))
    def oneActive(x,sx):
        got=mp(spec(HS,x),sJ(x,sx))
        return unpack(got,lambda y,h:unpack(ar(h),lambda i,e:ei(NE(Active),i,active_proof(i,x,y,sx,e))))
    NA=unpack(NS,oneActive)
    jj=fresh(Idx,'j');acov=For(jj,lambda jj:intro(App(Active,jj),lambda unused:spec(HallK,jj)))
    idxsource=apply(spec(apply(spec(inst(finite_source,X=Idx),Orel,CK),Hoi,Hot,HfinK),Active),acov,NA)
    def core_with_i(i,hi):
        acti=al(hi);imin=ar(hi);B=App(F,i)
        def block(j,x,z,earlier,sx,edge):
            return mp(mp(spec(imin,j),active_proof(j,x,z,sx,edge)),earlier)
        def blockEarlier(x,z,sx,prior):
            return unpack(prior,lambda j,p:block(j,x,z,al(p),sx,ar(p)))
        eqi=Eq(i,zero)
        def neqproof(eq):
            def withx(x,hx):
                def withz(z,h):
                    kk=fresh(Idx,'k');e0=eq_transport(eq,Lam(kk,apps(F,kk,x,z)),ar(h))
                    return mp(spec(sNo(x,al(h)),z),e0)
                return unpack(hx,withz)
            return unpack(acti,withx)
        i0=intro(eqi,neqproof)
        zz=fresh(X,'z');xx=fresh(X,'x');Targets=Lam(zz,Ex(xx,And(App(S,xx),apps(B,xx,zz))))
        def target_proof(z,x,sx,e):return ei(norm(App(Targets,z)),x,ai(sx,e))
        nt=unpack(acti,lambda x,hx:unpack(hx,lambda z,h:ei(NE(Targets),z,target_proof(z,x,al(h),ar(h)))))
        zz=fresh(X,'z')
        def target_j(z,p):
            return unpack(p,lambda x,h:ar(mp(spec(HD,x,z),use(color_total,[F,i,x,z],[ar(h)]))))
        tcov=For(zz,lambda zz:intro(App(Targets,zz),lambda p:mp(spec(HcoverX,zz),target_j(zz,p))))
        uu=fresh(X,'u');vv=fresh(X,'v');ww=fresh(X,'w');BT=Lam(uu,Lam(vv,Plus(B,uu,vv)))
        ir=mp(spec(wf_acyclic,B),spec(Hwf,i))
        tr=gens([uu,vv,ww],iis([Plus(B,uu,vv),Plus(B,vv,ww)],apply(spec(plus_trans,B,uu,vv,ww),hyp(Plus(B,uu,vv)),hyp(Plus(B,vv,ww)))))
        chosen=apply(spec(apply(spec(finite_source,BT,CX),ir,tr,HfinX),Targets),tcov,nt)
        def core_with_z(z,hz):
            vz=al(hz);zmin=ar(hz)
            def noLong(x,u,sx,bxu,tail):return mp(mp(spec(zmin,u),target_proof(u,x,sx,bxu)),tail)
            jz=target_j(z,vz)
            got=mp(spec(rep,z),jz)
            def core_with_t(t,ht):
                st=al(ht);repz=ar(ht)
                def totalB(x,z,e):return use(color_total,[F,i,x,z],[e])
                def noBt(e):
                    rtt=apply(spec(repz,t),st,totalB(t,z,e))
                    return mp(spec(mp(spec(union_irrefl,F),Hwf),t),rtt)
                nbt=intro(apps(B,t,z),noBt)
                x=fresh(X,'x');y=fresh(X,'y')
                def transfer_x(sx):
                    def transfer_y(sy):
                        def transfer_b(byz):
                            def transfer_edge(rxy):
                                # Exclude earlier and same-color edges; the edge is later.
                                def classify(j,e):
                                    def equal(eq):
                                        kk=fresh(Idx,'k');bxy=eq_transport(eq,Lam(kk,apps(F,kk,x,y)),e)
                                        return absurd(noLong(x,y,sx,bxy,use(plus_one,[B,y,z],[byz])),apps(Part(F,Orel,i),x,y))
                                    def strict(q):
                                        return cases(q,
                                            lambda prev:absurd(block(j,x,y,prev,sx,e),apps(Part(F,Orel,i),x,y)),
                                            lambda later:ei(norm(apps(Part(F,Orel,i),x,y)),j,ai(later,e)))
                                    return cases(spec(Hotri,j,i),equal,strict)
                                late=unpack(rxy,classify)
                                route=apply(spec(Hg,i,x,y,z),i0,late,byz)
                                def reject_detour(d):
                                    return unpack(d,lambda u,h:absurd(blockEarlier(x,u,sx,al(h)),apps(R,x,z)))
                                def other(o):
                                    def samepath(p):
                                        def withu(u,h):
                                            def equal(eq):
                                                ww=fresh(X,'w');bxz=eq_transport(eq,Lam(ww,apps(B,x,ww)),al(h));return totalB(x,z,bxz)
                                            def longer(tail):return absurd(noLong(x,u,sx,al(h),tail),apps(R,x,z))
                                            return cases(use(star_split,[B,u,z],[ar(h)]),equal,longer)
                                        return unpack(p,withu)
                                    return cases(o,samepath,lambda p:use(tail_total,[F,Orel,i,x,z],[p]))
                                rxz=cases(route,reject_detour,other)
                                return apply(spec(repz,x),sx,rxz)
                            return intro(apps(R,x,y),transfer_edge)
                        return intro(apps(B,y,z),transfer_b)
                    return intro(App(S,y),transfer_y)
                trf=gens([x,y],intro(App(S,x),transfer_x))
                xx=fresh(X,'x');Sp=Lam(xx,And(App(S,xx),Not(apps(B,xx,z))))
                sprep=use(fold_rep,[R,B,J,S,z,t],[rep,st,nbt,trf])
                spne=ei(NE(Sp),t,ai(st,nbt))
                sps=For(xx,lambda xx:intro(App(Sp,xx),lambda h:al(h)))
                spm=use(subset_trans,[Sp,S,M],[sps,SM])
                goodsp=ai(spne,ai(spm,sprep))
                ssp=apply(spec(Smin,Sp),sps,goodsp)
                return unpack(vz,lambda y,h:mp(ar(mp(spec(ssp,y),al(h))),ar(h)))
            return unpack(got,core_with_t)
        return unpack(chosen,core_with_z)
    return unpack(idxsource,core_with_i)
core=unpack(minimalS,core_with_S)
serial_family_impossible=lemma('serial_family_impossible',core,[F,Orel,zero,J,CX,CK],ass)

# Failure of well-foundedness gives a nonempty serial subset (classically).
R=fresh(Rel(X),'R');Q=fresh(Arr(X,O),'Q');x=fresh(X,'x');y=fresh(X,'y')
SS=Ex(Q,And(NE(Q),serial(R,Q)))
def notwf_to_serial(nos):
    # From absence of such a subset derive the full induction principle for R.
    H=fresh(Arr(X,O),'H');x=fresh(X,'x');y=fresh(X,'y')
    step=All(x,Imp(All(y,Imp(apps(R,x,y),App(H,y))),App(H,x)))
    def forstep(hstep):
        a=fresh(X,'a')
        def at_a(nha):
            v=fresh(X,'v');Bad=Lam(v,Not(App(H,v)));bad_ne=ei(NE(Bad),a,nha)
            xx=fresh(X,'x');yy=fresh(X,'y')
            def atx(nx):
                goal=Ex(yy,And(App(Bad,yy),apps(R,xx,yy)))
                def no_succ(nex):
                    vv=fresh(X,'v')
                    def aty(edge):
                        return by_contra(App(H,vv),lambda nv:mp(nex,ei(goal,vv,ai(nv,edge))))
                    allh=For(vv,lambda vv:intro(apps(R,xx,vv),aty))
                    return mp(nx,mp(spec(hstep,xx),allh))
                return by_contra(goal,no_succ)
            srl=For(xx,lambda xx:intro(App(Bad,xx),atx))
            return mp(nos,ei(SS,Bad,ai(bad_ne,srl)))
        return For(a,lambda a:by_contra(App(H,a),at_a))
    wf=For(H,lambda H:intro(step,forstep))
    return mp(hyp(Not(WF(R))),wf)
notwf_serial=lemma('not_wf_serial',by_contra(SS,notwf_to_serial),[R],[Not(WF(R))])

# Predecessor closure of a serial subset is itself serial and backward closed.
def PredClosure(R,S):
    x=fresh(X,'x');y=fresh(X,'y');return Lam(x,Ex(y,And(Star(R,x,y),App(S,y))))
def backward(R,J):
    x=fresh(X,'x');y=fresh(X,'y');return alls([x,y],imps([apps(R,x,y),App(J,y)],App(J,x)))
R=fresh(Rel(X),'R');S=fresh(Arr(X,O),'S');J=PredClosure(R,S);x=fresh(X,'x');y=fresh(X,'y')
def inJ(x,y,path,sy):return ei(norm(App(J,x)),y,ai(path,sy))
closure_ne=lemma('predecessor_closure_nonempty',unpack(hyp(NE(S)),lambda x,sx:ei(NE(J),x,inJ(x,x,spec(star_refl,R,x),sx))),[R,S],[NE(S)])
closure_back=lemma('predecessor_closure_backward',gens([x,y],intro(apps(R,x,y),lambda e:intro(App(J,y),lambda jy:unpack(jy,lambda z,h:inJ(x,z,use(star_cons,[R,x,y,z],[e,al(h)]),ar(h)))))),[R,S])

def closure_serial_at(x,jx):
    yy=fresh(X,'y');target=Ex(yy,And(App(J,yy),apps(R,x,yy)))
    def withy(y,h):
        def equal(eq):
            ww=fresh(X,'w');sx=eq_transport(reverse_eq(eq,x,y),Lam(ww,App(S,ww)),ar(h))
            got=mp(spec(hyp(serial(R,S)),x),sx)
            return unpack(got,lambda z,q:ei(target,z,ai(inJ(z,z,spec(star_refl,R,z),al(q)),ar(q))))
        def positive(p):
            return unpack(p,lambda u,q:ei(target,u,ai(inJ(u,y,ar(q),ar(h)),al(q))))
        return cases(use(star_split,[R,x,y],[al(h)]),equal,positive)
    return unpack(jx,withy)
x=fresh(X,'x')
closure_serial=lemma('predecessor_closure_serial',For(x,lambda x:intro(App(J,x),lambda jx:closure_serial_at(x,jx))),[R,S],[serial(R,S)])

# Restriction to a backward-closed subset preserves every witness ending there.
def Cut(J,R):
    ty=type_of(J)[1];x=fresh(ty,'x');y=fresh(ty,'y');return Lam(x,Lam(y,And(App(J,x),And(apps(R,x,y),App(J,y)))))
R=fresh(Rel(X),'R');J=fresh(Arr(X,O),'J');x=fresh(X,'x');y=fresh(X,'y');u=fresh(X,'u');v=fresh(X,'v')
CR=Cut(J,R);h=Lam(u,And(App(J,u),Star(CR,u,y)))
base=ai(hyp(App(J,y)),spec(star_refl,CR,y))
def restrict_step(e):
    def ih(q):
        ju=apply(spec(hyp(backward(R,J)),u,v),e,al(q))
        cutedge=ai(ju,ai(e,al(q)))
        return ai(ju,use(star_cons,[CR,u,v,y],[cutedge,ar(q)]))
    return intro(And(App(J,v),Star(CR,v,y)),ih)
step=gens([u,v],intro(apps(R,u,v),restrict_step))
star_cut=lemma('star_restrict',apply(spec(hyp(Star(R,x,y)),h),base,step),[R,J,x,y],[backward(R,J),Star(R,x,y),App(J,y)])
# Forward paths also transport backward-closed membership alone.
star_back=lemma('star_backward',al(use(star_cut,[R,J,x,y],[hyp(backward(R,J)),hyp(Star(R,x,y)),hyp(App(J,y))])),[R,J,x,y],[backward(R,J),Star(R,x,y),App(J,y)])

# Explicit family restriction and its exact union correspondence.
def CutFamily(J,F):
    i=fresh(Idx,'i');return Lam(i,Cut(J,App(F,i)))
F=fresh(FamTy,'F');J=fresh(Arr(X,O),'J');CF=CutFamily(J,F);R=Total(F);RC=Total(CF)
x=fresh(X,'x');y=fresh(X,'y');i=fresh(Idx,'i')
cut_to_total=lemma('restricted_union_to_cut',unpack(hyp(apps(RC,x,y)),lambda i,h:ai(al(h),ai(use(color_total,[F,i,x,y],[al(ar(h))]),ar(ar(h))))),[F,J,x,y],[apps(RC,x,y)])
cut_from_total=lemma('cut_to_restricted_union',unpack(al(ar(hyp(apps(Cut(J,R),x,y)))),lambda i,h:use(color_total,[CF,i,x,y],[ai(al(hyp(apps(Cut(J,R),x,y))),ai(h,ar(ar(hyp(apps(Cut(J,R),x,y))))))])),[F,J,x,y],[apps(Cut(J,R),x,y)])
# Each restricted color is still well-founded.
u=fresh(X,'u');v=fresh(X,'v');i=fresh(Idx,'i')
sub=gens([u,v],intro(apps(CF,i,u,v),lambda h:al(ar(h))))
cut_wf=lemma('restricted_colors_wf',For(i,lambda i:use(wf_mono,[App(CF,i),App(F,i)],[sub,spec(hyp(WFcolors(F)),i)])),[F,J],[WFcolors(F)])
cut_domain=lemma('restricted_domain',gens([x,y],intro(apps(RC,x,y),lambda h:unpack(h,lambda i,q:ai(al(q),ar(ar(q)))))),[F,J])
cut_serial=lemma('restricted_serial',For(x,lambda x:intro(App(J,x),lambda jx:unpack(mp(spec(hyp(serial(R,J)),x),jx),lambda y,h:ei(serial_target(RC,J,x),y,ai(al(h),use(cut_from_total,[F,J,x,y],[ai(jx,ai(ar(h),al(h)))])))))),[F,J],[serial(R,J)])


# Earlier and later subunions commute with endpoint restriction.
F=fresh(FamTy,'F');J=fresh(Arr(X,O),'J');Orel=fresh(Rel(Idx),'order');CF=CutFamily(J,F);i=fresh(Idx,'i');x=fresh(X,'x');y=fresh(X,'y')
def make_part_lemmas(earlier):
    P0=Part(F,Orel,i,earlier);P1=Part(CF,Orel,i,earlier)
    def out(j,h):
        e=ar(h)
        old=ei(norm(apps(P0,x,y)),j,ai(al(h),al(ar(e))))
        return ai(al(e),ai(old,ar(ar(e))))
    outproof=lemma(('earlier' if earlier else 'tail')+'_restriction_out',unpack(hyp(apps(P1,x,y)),out),[F,J,Orel,i,x,y],[apps(P1,x,y)])
    def inside(j,h):
        new=ai(hyp(App(J,x)),ai(ar(h),hyp(App(J,y))))
        return ei(norm(apps(P1,x,y)),j,ai(al(h),new))
    inproof=lemma(('earlier' if earlier else 'tail')+'_restriction_in',unpack(hyp(apps(P0,x,y)),inside),[F,J,Orel,i,x,y],[App(J,x),apps(P0,x,y),App(J,y)])
    return outproof,inproof
cut_tail_out,cut_tail_in=make_part_lemmas(False)
cut_early_out,cut_early_in=make_part_lemmas(True)
R=Total(F);RC=Total(CF);u=fresh(X,'u');v=fresh(X,'v')
cut_inc=gens([u,v],intro(apps(Cut(J,R),u,v),lambda h:use(cut_from_total,[F,J,u,v],[h])))
s=use(star_cut,[R,J,x,y],[hyp(backward(R,J)),hyp(Star(R,x,y)),hyp(App(J,y))])
sr=use(star_mono,[Cut(J,R),RC,x,y],[cut_inc,ar(s)])
star_family_cut=lemma('star_family_restriction',ai(al(s),sr),[F,J,x,y],[backward(R,J),Star(R,x,y),App(J,y)])

# Positive single-color paths retain all their witnesses.
i=fresh(Idx,'i');B=App(F,i);BC=App(CF,i);R=Total(F)
u=fresh(X,'u');v=fresh(X,'v')
bback=gens([u,v],intro(apps(B,u,v),lambda e:intro(App(J,v),lambda jv:apply(spec(hyp(backward(R,J)),u,v),use(color_total,[F,i,u,v],[e]),jv))))
def plus_cut_at(u,h):
    got=use(star_cut,[B,J,u,y],[bback,ar(h),hyp(App(J,y))])
    ju=al(got);tail=ar(got)
    jx=apply(spec(hyp(backward(R,J)),x,u),use(color_total,[F,i,x,u],[al(h)]),ju)
    edge=ai(jx,ai(al(h),ju))
    return ai(jx,ei(Plus(BC,x,y),u,ai(edge,tail)))
plus_family_cut=lemma('plus_family_restriction',unpack(hyp(Plus(B,x,y)),plus_cut_at),[F,J,i,x,y],[backward(R,J),Plus(B,x,y),App(J,y)])

# The full interaction conditions are preserved, including every alternative.
zero=fresh(Idx,'zero');x=fresh(X,'x');y=fresh(X,'y');z=fresh(X,'z');A=App(F,zero);AC=App(CF,zero)
T=Part(F,Orel,zero);TC=Part(CF,Orel,zero)
def gzero_at(tcut):
    endpoints=use(cut_tail_out,[F,J,Orel,zero,x,y],[tcut]);jx=al(endpoints);oldtail=al(ar(endpoints))
    def atedge(acut):
        olda=al(ar(acut));jz=ar(ar(acut));route=apply(spec(hyp(Gzero(F,Orel,zero)),x,y,z),oldtail,olda)
        def det(d):
            def getu(u,h):
                s=use(star_family_cut,[F,J,u,z],[hyp(backward(R,J)),ar(h),jz])
                ac=ai(jx,ai(al(h),al(s)))
                return ol(ei(Detour(AC,RC,x,z),u,ai(ac,ar(s))),apps(TC,x,z))
            return unpack(d,getu)
        def short(p):
            return ore(use(cut_tail_in,[F,J,Orel,zero,x,z],[jx,p,jz]),Detour(AC,RC,x,z))
        return cases(route,det,short)
    return intro(apps(AC,y,z),atedge)
gz=gens([x,y,z],intro(apps(TC,x,y),gzero_at))
cut_gzero=lemma('restricted_G0',gz,[F,J,Orel,zero],[backward(R,J),Gzero(F,Orel,zero)])

i=fresh(Idx,'i');x=fresh(X,'x');y=fresh(X,'y');z=fresh(X,'z');B=App(F,i);BC=App(CF,i)
T=Part(F,Orel,i);TC=Part(CF,Orel,i);Pold=Part(F,Orel,i,True);PC=Part(CF,Orel,i,True)
def gothers_at(nzi):
    def at_tail(tcut):
        endpoints=use(cut_tail_out,[F,J,Orel,i,x,y],[tcut]);jx=al(endpoints);oldtail=al(ar(endpoints))
        def atedge(bcut):
            oldb=al(ar(bcut));jz=ar(ar(bcut));route=apply(spec(hyp(Gothers(F,Orel,zero)),i,x,y,z),nzi,oldtail,oldb)
            def det(d):
                def getu(u,h):
                    s=use(star_family_cut,[F,J,u,z],[hyp(backward(R,J)),ar(h),jz])
                    prior=use(cut_early_in,[F,J,Orel,i,x,u],[jx,al(h),al(s)])
                    return ol(ei(Detour(PC,RC,x,z),u,ai(prior,ar(s))),Or(Plus(BC,x,z),apps(TC,x,z)))
                return unpack(d,getu)
            def rest(r):
                def plus(p):
                    q=ar(use(plus_family_cut,[F,J,i,x,z],[hyp(backward(R,J)),p,jz]))
                    return ore(ol(q,apps(TC,x,z)),Detour(PC,RC,x,z))
                def shortcut(p):
                    q=use(cut_tail_in,[F,J,Orel,i,x,z],[jx,p,jz])
                    return ore(ore(q,Plus(BC,x,z)),Detour(PC,RC,x,z))
                return cases(r,plus,shortcut)
            return cases(route,det,rest)
        return intro(apps(BC,y,z),atedge)
    return intro(apps(TC,x,y),at_tail)
gs=gens([i,x,y,z],intro(Not(Eq(i,zero)),gothers_at))
cut_gothers=lemma('restricted_Gi',gs,[F,J,Orel,zero],[backward(R,J),Gothers(F,Orel,zero)])

# Main theorem: arbitrary finite ordered families on arbitrary finite domains.
F=fresh(FamTy,'F');Orel=fresh(Rel(Idx),'order');zero=fresh(Idx,'zero')
CX=fresh(Arr(X,O),'coverX');CK=fresh(Arr(Idx,O),'coverK');x=fresh(X,'x');i=fresh(Idx,'i')
allX=All(x,App(CX,x));allK=All(i,App(CK,i));R=Total(F)
ass=[Fin(CX),allX,Fin(CK),allK,irrefl(Orel),trans(Orel),tri(Orel),least(Orel,zero),WFcolors(F),Gzero(F,Orel,zero),Gothers(F,Orel,zero)]
FX,AX,FK,AK,OI,OT,OTT,ZL,WFC,GZ,GI=map(hyp,ass)
def prove_full(notwf):
    witness=mp(spec(notwf_serial,R),notwf)
    def with_bad(S,h):
        J=PredClosure(R,S);CF=CutFamily(J,F);RC=Total(CF)
        jne=use(closure_ne,[R,S],[al(h)]);jb=spec(closure_back,R,S);js=use(closure_serial,[R,S],[ar(h)])
        xx=fresh(X,'x');jc=For(xx,lambda xx:intro(App(J,xx),lambda unused:spec(AX,xx)))
        wc=use(cut_wf,[F,J],[WFC]);dc=spec(cut_domain,F,J);sc=use(cut_serial,[F,J],[js])
        zg=use(cut_gzero,[F,J,Orel,zero],[jb,GZ]);ig=use(cut_gothers,[F,J,Orel,zero],[jb,GI])
        return use(serial_family_impossible,[CF,Orel,zero,J,CX,CK],[FX,jc,FK,AK,OI,OT,OTT,ZL,wc,zg,ig,dc,jne,sc])
    return unpack(witness,with_bad)
finite_family=lemma('finite_family_termination',by_contra(WF(R),prove_full),[F,Orel,zero,CX,CK],ass)

# Closed finite-domain quantifiers rather than explicit covering predicates.
def FinType(T):
    c=fresh(Arr(T,O),'C');x=fresh(T,'x');return Ex(c,And(Fin(c),All(x,App(c,x))))
ass2=[FinType(X),FinType(Idx),irrefl(Orel),trans(Orel),tri(Orel),least(Orel,zero),WFcolors(F),Gzero(F,Orel,zero),Gothers(F,Orel,zero)]
rest=list(map(hyp,ass2[2:]))
main=unpack(hyp(ass2[0]),lambda cx,hx:unpack(hyp(ass2[1]),lambda ck,hk:
    use(finite_family,[F,Orel,zero,cx,ck],[al(hx),ar(hx),al(hk),ar(hk)]+rest)))
main_theorem=lemma('arbitrary_finite_family_well_founded_union',main,[F,Orel,zero],ass2)

# Finiteness constructors make the ordinary finite-enumeration interpretation explicit.
S=fresh(Arr(X,O),'S');a=fresh(X,'a');Q=fresh(Arr(Arr(X,O),O),'Q');s=fresh(Arr(X,O),'S');x=fresh(X,'x')
step=All(x,All(s,Imp(App(Q,s),App(Q,Ins(x,s)))))
finite_empty=lemma('finite_empty',For(Q,lambda Q:iis([App(Q,Empty(X)),step],hyp(App(Q,Empty(X))))))
insert=For(Q,lambda Q:intro(App(Q,Empty(X)),lambda base:intro(step,lambda st:
    mp(spec(st,a,S),apply(spec(hyp(Fin(S)),Q),base,st)))))
finite_insert=lemma('finite_insert',insert,[S,a],[Fin(S)])

# On a finite domain, acyclicity entails the standard induction principle.
R=fresh(Rel(X),'R');C=fresh(Arr(X,O),'C');x=fresh(X,'x');u=fresh(X,'u');v=fresh(X,'v');w=fresh(X,'w')
cover=All(x,App(C,x));acyclic=All(x,Not(Plus(R,x,x)))
Rev=Lam(u,Lam(v,Plus(R,v,u)))
rev_ir=hyp(acyclic)
rev_tr=gens([u,v,w],iis([Plus(R,v,u),Plus(R,w,v)],apply(spec(plus_trans,R,w,v,u),hyp(Plus(R,w,v)),hyp(Plus(R,v,u)))))
src_all=apply(spec(finite_source,Rev,C),rev_ir,rev_tr,hyp(Fin(C)))
H=fresh(Arr(X,O),'H');x=fresh(X,'x');y=fresh(X,'y')
step=All(x,Imp(All(y,Imp(apps(R,x,y),App(H,y))),App(H,x)))
def induction_step(st):
    a=fresh(X,'a');vv=fresh(X,'v');Bad=Lam(vv,Not(App(H,vv)))
    def bad_a(na):
        xx=fresh(X,'x');bc=For(xx,lambda xx:intro(App(Bad,xx),lambda unused:spec(hyp(cover),xx)))
        chosen=apply(spec(src_all,Bad),bc,ei(NE(Bad),a,na))
        def atmin(x,h):
            nx=al(h);mn=ar(h);yy=fresh(X,'y')
            allh=For(yy,lambda yy:intro(apps(R,x,yy),lambda e:by_contra(App(H,yy),lambda ny:
                mp(mp(spec(mn,yy),ny),use(plus_one,[R,x,yy],[e])))))
            return mp(nx,mp(spec(st,x),allh))
        return unpack(chosen,atmin)
    return For(a,lambda a:by_contra(App(H,a),bad_a))
finite_acyclic_wf=lemma('finite_acyclic_well_founded',For(H,lambda H:intro(step,induction_step)),[R,C],[Fin(C),cover,acyclic])

# The acyclic finite-family version, exactly the hypothesis form in the paper.
F=fresh(FamTy,'F');Orel=fresh(Rel(Idx),'order');zero=fresh(Idx,'zero');CX=fresh(Arr(X,O),'coverX');CK=fresh(Arr(Idx,O),'coverK');x=fresh(X,'x');i=fresh(Idx,'i')
allX=All(x,App(CX,x));allK=All(i,App(CK,i));acycColors=All(i,All(x,Not(Plus(App(F,i),x,x))))
ass=[Fin(CX),allX,Fin(CK),allK,irrefl(Orel),trans(Orel),tri(Orel),least(Orel,zero),acycColors,Gzero(F,Orel,zero),Gothers(F,Orel,zero)]
hh=list(map(hyp,ass))
wfcs=For(i,lambda i:use(finite_acyclic_wf,[App(F,i),CX],[hh[0],hh[1],spec(hh[8],i)]))
finacyc=use(finite_family,[F,Orel,zero,CX,CK],hh[:8]+[wfcs]+hh[9:])
finite_acyclic_family=lemma('finite_acyclic_family_termination',finacyc,[F,Orel,zero,CX,CK],ass)
ass2=[FinType(X),FinType(Idx),irrefl(Orel),trans(Orel),tri(Orel),least(Orel,zero),acycColors,Gzero(F,Orel,zero),Gothers(F,Orel,zero)]
rest=list(map(hyp,ass2[2:]))
closed=unpack(hyp(ass2[0]),lambda cx,hx:unpack(hyp(ass2[1]),lambda ck,hk:
    use(finite_acyclic_family,[F,Orel,zero,cx,ck],[al(hx),ar(hx),al(hk),ar(hk)]+rest)))
main_acyclic=lemma('arbitrary_finite_acyclic_family_termination',closed,[F,Orel,zero],ass2)

# A forward chain indexed by any inhabited successor type contradicts WF.
N='N';R=fresh(Rel(X),'R');f=fresh(Arr(N,X),'f');s=fresh(Arr(N,N),'next');a=fresh(N,'start');n=fresh(N,'n');x=fresh(X,'x')
chain=All(n,apps(R,App(f,n),App(f,App(s,n))))
Range=Lam(x,Ex(n,Eq(x,App(f,n))))
nrng=ei(NE(Range),App(f,a),ei(norm(App(Range,App(f,a))),a,refl(App(f,a))))
x=fresh(X,'x')
def range_at(rx):
    def withn(n,eq):
        nxt=App(f,App(s,n));w=fresh(X,'w')
        e=eq_transport(reverse_eq(eq,x,App(f,n)),Lam(w,apps(R,w,nxt)),spec(hyp(chain),n))
        mem=ei(norm(App(Range,nxt)),App(s,n),refl(nxt))
        return ei(serial_target(R,Range,x),nxt,ai(mem,e))
    return unpack(rx,withn)
srng=For(x,lambda x:intro(App(Range,x),range_at))
wf_no_chain=lemma('well_founded_excludes_forward_chain',use(wf_no_serial,[R,Range],[hyp(WF(R)),nrng,srng]),[R,f,s,a],[WF(R),chain])

print('ALL DONE',len(K.records),'steps;',len(THEOREMS),'closed theorems')
# Base certificate remains in memory for the branching extension.
