"""Checked layer-height and ordinal extensions. No new kernel rules."""
from build_branching import *
EXTENSION_START = frozenset(THEOREMS)

def tri(R):
    T=type_of(R)[1];a=fresh(T,'a');b=fresh(T,'b')
    return alls([a,b],Or(Eq(a,b),Or(apps(R,a,b),apps(R,b,a))))


def TotalOn(F,C):
    x=fresh(X,'x');y=fresh(X,'y');i=fresh(Idx,'i')
    return Lam(x,Lam(y,Ex(i,And(App(C,i),apps(F,i,x,y)))))

def TransWF(R):
    T=fresh(Rel(X),'T')
    return All(T,imps([SubRel(T,R),trans(T)],WF(T)))

def Cut(S,R):
    x=fresh(X,'x');y=fresh(X,'y')
    return Lam(x,Lam(y,CAnd(App(S,x),apps(R,x,y),App(S,y))))

# A finite union of well-founded relations has only well-founded transitive
# subrelations, without any interaction hypothesis.
def make_transitive_union():
    F=fresh(FamTy,'F');C=fresh(Arr(Idx,O),'C');T=fresh(Rel(X),'T')
    WFC=hyp(WFcolors(F))
    def prop(C):return TransWF(TotalOn(F,C))
    x=fresh(X,'x');y=fresh(X,'y');S=fresh(Arr(X,O),'S')
    def base_sub(st):
        def base_tr(tt):
            # Empty relation: every predicate is inductive trivially.
            H=fresh(Arr(X,O),'H');a=fresh(X,'a');b=fresh(X,'b')
            step=All(a,Imp(All(b,Imp(apps(T,a,b),App(H,b))),App(H,a)))
            def at(a):
                nob=For(b,lambda b:intro(apps(T,a,b),lambda e:unpack(mp(spec(st,a,b),e),lambda i,h:absurd(al(h),App(H,b)))))
                return mp(spec(hyp(step),a),nob)
            return For(H,lambda H:intro(step,lambda _:For(a,at)))
        return intro(trans(T),base_tr)
    base=For(T,lambda T:intro(SubRel(T,TotalOn(F,Empty(Idx))),base_sub))
    a=fresh(Idx,'a');U=fresh(Arr(Idx,O),'U')
    def insert(ih):
        def withsub(st):
            def withtr(tt):
                def nw(notwf):
                    serialset=use(notwf_serial,[T],[notwf])
                    def withJ(J,hJ):
                        NJ,SJ=al(hJ),ar(hJ)
                        x=fresh(X,'x');y=fresh(X,'y')
                        P0=Lam(x,Lam(y,CAnd(App(J,x),apps(T,x,y),apps(F,a,x,y),App(J,y))))
                        subP=gens([x,y],intro(apps(P0,x,y),lambda h:proj(h,2,4)))
                        WP=use(wf_mono,[P0,App(F,a)],[subP,spec(WFC,a)])
                        M=Lam(x,And(App(J,x),No(P0,x)))
                        def normalj(u,ju):
                            z=fresh(X,'z');target=Ex(z,And(App(M,z),Star(P0,u,z)))
                            nf=spec(use(wf_normal,[P0],[WP]),u)
                            def got(t,ht):
                                v=fresh(X,'v');w=fresh(X,'w')
                                forward=gens([v,w],intro(apps(P0,v,w),lambda h:intro(App(J,v),lambda _:proj(h,3,4))))
                                jt=use(star_forward,[P0,J,u,t],[forward,al(ht),ju])
                                return ei(target,t,ai(ai(jt,ar(ht)),al(ht)))
                            return unpack(nf,got)
                        NM=unpack(NJ,lambda u,ju:unpack(normalj(u,ju),lambda t,ht:ei(NE(M),t,al(ht))))
                        def serialm(mx):
                            def at_u(u,hu):
                                def at_t(t,ht):
                                    v=fresh(X,'v');w=fresh(X,'w')
                                    pred=Lam(v,apps(T,x,v))
                                    step=gens([v,w],intro(apps(P0,v,w),lambda h:intro(apps(T,x,v),lambda e:apply(spec(tt,x,v,w),e,proj(h,1,4)))))
                                    txt=use(star_forward,[P0,pred,u,t],[step,ar(ht),ar(hu)])
                                    return ei(serial_target(T,M,x),t,ai(al(ht),txt))
                                return unpack(normalj(u,al(hu)),at_t)
                            return unpack(mp(spec(SJ,x),al(mx)),at_u)
                        SM=For(x,lambda x:intro(App(M,x),serialm))
                        Q=Cut(M,T);v=fresh(X,'v');w=fresh(X,'w');z=fresh(X,'z')
                        def smaller(h):
                            mx,txy,my=[proj(h,j,3) for j in range(3)]
                            def col(i,hi):
                                def eqi(eq):
                                    k=fresh(Idx,'k');eax=eq_transport(eq,Lam(k,apps(F,k,v,w)),ar(hi))
                                    pe=cproof(al(mx),txy,eax,al(my))
                                    return absurd(mp(spec(ar(mx),w),pe),apps(TotalOn(F,U),v,w))
                                return cases(al(hi),eqi,lambda ui:ei(norm(apps(TotalOn(F,U),v,w)),i,ai(ui,ar(hi))))
                            return unpack(mp(spec(st,v,w),txy),col)
                        subQ=gens([v,w],intro(apps(Q,v,w),smaller))
                        def trQ(h1):
                            return intro(apps(Q,w,z),lambda h2:cproof(proj(h1,0,3),apply(spec(tt,v,w,z),proj(h1,1,3),proj(h2,1,3)),proj(h2,2,3)))
                        tq=gens([v,w,z],intro(apps(Q,v,w),trQ))
                        WQ=apply(spec(ih,Q),subQ,tq)
                        def sq(mx):
                            return unpack(mp(spec(SM,x),mx),lambda y,hy:ei(serial_target(Q,M,x),y,ai(al(hy),cproof(mx,ar(hy),al(hy)))))
                        SQ=For(x,lambda x:intro(App(M,x),sq))
                        return use(wf_no_serial,[Q,M],[WQ,NM,SQ])
                    return unpack(serialset,withJ)
                return by_contra(WF(T),nw)
            return intro(trans(T),withtr)
        return For(T,lambda T:intro(SubRel(T,TotalOn(F,Ins(a,U))),withsub))
    step=gens([a,U],intro(prop(U),insert))
    q=fresh(Arr(Idx,O),'C')
    out=apply(spec(hyp(Fin(C)),Lam(q,prop(q))),base,step)
    return lemma('finite_union_transitive_subrelation_well_founded',out,[F,C],[WFcolors(F),Fin(C)])
transitive_union=make_transitive_union()


def make_total_transwf():
    F=fresh(FamTy,'F');C=fresh(Arr(Idx,O),'C');i=fresh(Idx,'i');T=fresh(Rel(X),'T')
    ass=[WFcolors(F),Fin(C),All(i,App(C,i))]
    W,FCc,AllC=map(hyp,ass)
    def st(sub):
        x=fresh(X,'x');y=fresh(X,'y')
        restricted=gens([x,y],intro(apps(T,x,y),lambda h:unpack(mp(spec(sub,x,y),h),lambda j,e:ei(norm(apps(TotalOn(F,C),x,y)),j,ai(spec(AllC,j),e)))))
        return intro(trans(T),lambda tr:apply(spec(use(transitive_union,[F,C],[W,FCc]),T),restricted,tr))
    return lemma('family_union_transitive_subrelations_well_founded',For(T,lambda T:intro(SubRel(T,Total(F)),st)),[F,C],ass)
family_transwf=make_total_transwf()

# Domination preserves all incoming edges from S, not merely edges of a color.
def Dominate(R,S):
    x=fresh(X,'x');y=fresh(X,'y');u=fresh(X,'u')
    return Lam(x,Lam(y,CAnd(App(S,x),App(S,y),apps(R,x,y),All(u,imps([App(S,u),apps(R,u,x)],apps(R,u,y))))))

def make_domination_wf():
    R=fresh(Rel(X),'R');S=fresh(Arr(X,O),'S');D=Dominate(R,S)
    x=fresh(X,'x');y=fresh(X,'y');z=fresh(X,'z');u=fresh(X,'u')
    sub=gens([x,y],intro(apps(D,x,y),lambda h:proj(h,2,4)))
    def hx(h):
        def hy(k):
            r=apply(spec(proj(k,3,4),x),proj(h,0,4),proj(h,2,4))
            tr=For(u,lambda u:intro(App(S,u),lambda su:intro(apps(R,u,x),lambda ux:apply(spec(proj(k,3,4),u),su,apply(spec(proj(h,3,4),u),su,ux)))))
            return cproof(proj(h,0,4),proj(k,1,4),r,tr)
        return intro(apps(D,y,z),hy)
    tr=gens([x,y,z],intro(apps(D,x,y),hx))
    out=apply(spec(hyp(TransWF(R)),D),sub,tr)
    return lemma('representative_domination_well_founded',out,[R,S],[TransWF(R)])
domination_wf=make_domination_wf()

# Remove a layer U when every point of U has a domination successor in S.
def make_remove_layer():
    R=fresh(Rel(X),'R');J=fresh(Arr(X,O),'J');S=fresh(Arr(X,O),'S');U=fresh(Arr(X,O),'U')
    D=Dominate(R,S);x=fresh(X,'x');t=fresh(X,'t')
    succ=All(x,Imp(App(U,x),Ex(t,apps(D,x,t))))
    ass=[TransWF(R),NE(S),Rep(R,J,S),Sub(U,S),succ]
    TW,NS,RepS,US,Succ=map(hyp,ass)
    Vv=Lam(x,And(App(S,x),Not(App(U,x))))
    def endpoint(x):
        t=fresh(X,'t');return Ex(t,And(App(Vv,t),Star(D,x,t)))
    ih=All(t,Imp(apps(D,x,t),Imp(App(S,t),endpoint(t))))
    def step(hi):
        def sx(sx):
            def inU(ux):
                def at_t(t,dt):
                    got=apply(spec(hi,t),dt,proj(dt,1,4))
                    return unpack(got,lambda v,h:ei(endpoint(x),v,ai(al(h),use(star_cons,[D,x,t,v],[dt,ar(h)]))))
                return unpack(mp(spec(Succ,x),ux),at_t)
            def outside(nu):return ei(endpoint(x),x,ai(ai(sx,nu),spec(star_refl,D,x)))
            return cases(em(App(U,x)),inU,outside)
        return intro(App(S,x),sx)
    induction=For(x,lambda x:intro(ih,step))
    pred=Lam(x,Imp(App(S,x),endpoint(x)))
    ends=mp(spec(use(domination_wf,[R,S],[TW]),pred),induction)
    NV=unpack(NS,lambda a,sa:unpack(mp(spec(ends,a),sa),lambda t,h:ei(NE(Vv),t,al(h))))
    z=fresh(X,'z');x=fresh(X,'x')
    def repz(jz):
        def at_u(u,hu):
            def at_v(v,hv):
                def incoming(vx):
                    def edge(rxz):
                        rxu=apply(spec(ar(hu),x),al(vx),rxz)
                        a=fresh(X,'a');b=fresh(X,'b')
                        pr=Lam(a,apps(R,x,a))
                        step=gens([a,b],intro(apps(D,a,b),lambda dab:intro(apps(R,x,a),lambda rxa:apply(spec(proj(dab,3,4),x),al(vx),rxa))))
                        return use(star_forward,[D,pr,u,v],[step,ar(hv),rxu])
                    return intro(apps(R,x,z),edge)
                rep=For(x,lambda x:intro(App(Vv,x),incoming))
                return ei(rep_target(R,J,Vv,z),v,ai(al(hv),rep))
            return unpack(mp(spec(ends,u),al(hu)),at_v)
        return unpack(mp(spec(RepS,z),jz),at_u)
    RV=For(z,lambda z:intro(App(J,z),repz))
    VS=For(x,lambda x:intro(App(Vv,x),lambda h:al(h)))
    return lemma('successor_layer_removal_preserves_representatives',cproof(VS,NV,RV),[R,J,S,U],ass)
remove_layer=make_remove_layer()


# Height profiles are finite iterations of B-predecessor closure, starting
# from the empty predicate. Next(B,H_k) is exactly height <= k.
def Next(B,H):
    x=fresh(X,'x');y=fresh(X,'y')
    return Lam(x,All(y,Imp(apps(B,x,y),App(H,y))))
def HeightProfile(B,H):
    Q=fresh(Arr(Arr(X,O),O),'Q');U=fresh(Arr(X,O),'U')
    return All(Q,imps([App(Q,Empty(X)),All(U,Imp(App(Q,U),App(Q,Next(B,U))))],App(Q,H)))
def ForwardClosed(B,H):
    x=fresh(X,'x');y=fresh(X,'y')
    return alls([x,y],imps([apps(B,x,y),App(H,x)],App(H,y)))
def Bounded(B,S):
    H=fresh(Arr(X,O),'H')
    return Ex(H,And(HeightProfile(B,H),Sub(S,Next(B,H))))
def PointwiseBounded(B,S):
    x=fresh(X,'x');H=fresh(Arr(X,O),'H')
    return All(x,Imp(App(S,x),Ex(H,And(HeightProfile(B,H),App(Next(B,H),x)))))

def make_profile_constructors():
    B=fresh(Rel(X),'B');H=fresh(Arr(X,O),'H');Q=fresh(Arr(Arr(X,O),O),'Q');U=fresh(Arr(X,O),'U')
    base=App(Q,Empty(X));step=All(U,Imp(App(Q,U),App(Q,Next(B,U))))
    p0=lemma('height_profile_zero',gens([Q],iis([base,step],hyp(base))),[B])
    val=apply(spec(hyp(HeightProfile(B,H)),Q),hyp(base),hyp(step))
    pn=gens([Q],iis([base,step],mp(spec(hyp(step),H),val)))
    return p0,lemma('height_profile_successor',pn,[B,H],[HeightProfile(B,H)])
profile_zero,profile_succ=make_profile_constructors()


def make_uniform_stage():
    R=fresh(Rel(X),'R');B=fresh(Rel(X),'B');J=fresh(Arr(X,O),'J');H=fresh(Arr(X,O),'H')
    glob=[TransWF(R),SubRel(B,R),domain(R,J)]
    TW,BR,DJ=map(hyp,glob)
    def stage_ass(S,H):return [Sub(S,J),NE(S),Rep(R,J,S),LocalRoute(R,B,S),Sub(S,Next(B,H))]
    def property(H):
        S=fresh(Arr(X,O),'S')
        return And(ForwardClosed(B,H),All(S,imps(stage_ass(S,H),Clear(R,B,J,S))))
    x=fresh(X,'x');y=fresh(X,'y');S=fresh(Arr(X,O),'S')
    closed0=gens([x,y],iis([apps(B,x,y),App(Empty(X),x)],hyp(App(Empty(X),x))))
    def baseS():
        hs=stage_ass(S,Empty(X));SJ,NS,RS,Route,Bd=map(hyp,hs)
        no=For(x,lambda x:intro(App(S,x),lambda sx:For(y,lambda y:intro(apps(B,x,y),lambda e:mp(spec(mp(spec(Bd,x),sx),y),e)))))
        out=ei(Clear(R,B,J,S),S,cproof(spec(subset_refl,S),NS,RS,no))
        return gens([S],iis(hs,out))
    base=ai(closed0,baseS())
    Q=fresh(Arr(X,O),'Q')
    def step(ih):
        Closed=al(ih);IH=ar(ih);Hq=Next(B,Q)
        x=fresh(X,'x');y=fresh(X,'y');z=fresh(X,'z')
        def close(e):
            def hnext(nx):
                qy=mp(spec(nx,y),e)
                return For(z,lambda z:intro(apps(B,y,z),lambda yz:apply(spec(Closed,y,z),yz,qy)))
            return intro(App(Hq,x),hnext)
        closednext=gens([x,y],intro(apps(B,x,y),close))
        S=fresh(Arr(X,O),'S');hs=stage_ass(S,Hq);SJ,NS,RS,Route,Bd=map(hyp,hs)
        U=Lam(x,And(App(S,x),Not(App(Hq,x))))
        US=For(x,lambda x:intro(App(U,x),lambda u:al(u)))
        D=Dominate(R,S);y=fresh(X,'y');z=fresh(X,'z')
        def succu(uy):
            sy,nhy=al(uy),ar(uy)
            target=Ex(z,And(apps(B,y,z),Not(App(Q,z))))
            def no_target(nt):
                qz=For(z,lambda z:intro(apps(B,y,z),lambda e:by_contra(App(Q,z),lambda nq:mp(nt,ei(target,z,ai(e,nq))))))
                return mp(nhy,qz)
            got=by_contra(target,no_target)
            def atz(z,hz):
                byz,nqz=al(hz),ar(hz)
                jz=ar(mp(spec(DJ,y,z),mp(spec(BR,y,z),byz)))
                def att(t,ht):
                    st,rep=al(ht),ar(ht)
                    ryt=apply(spec(rep,y),sy,mp(spec(BR,y,z),byz))
                    x=fresh(X,'x')
                    def incoming(sx):
                        def re(rxy):
                            routes=apply(spec(Route,x,y,z),sx,sy,rxy,byz)
                            def pp(pxz):
                                def first(u,hu):
                                    b_xu,path=al(hu),ar(hu)
                                    nu=mp(spec(mp(spec(Bd,x),sx),u),b_xu)
                                    def eqcase(eq):
                                        v=fresh(X,'v');bxz=eq_transport(eq,Lam(v,apps(B,x,v)),b_xu)
                                        return mp(spec(BR,x,z),bxz)
                                    def positive(puz):
                                        def atv(v,hv):
                                            qv=mp(spec(nu,v),al(hv))
                                            qz=use(star_forward,[B,Q,v,z],[Closed,ar(hv),qv])
                                            return absurd(mp(nqz,qz),apps(R,x,z))
                                        return unpack(puz,atv)
                                    return cases(use(star_split,[B,u,z],[path]),eqcase,positive)
                                return unpack(pxz,first)
                            rxz=cases(routes,pp,lambda e:e)
                            return apply(spec(rep,x),sx,rxz)
                        return intro(apps(R,x,y),re)
                    inc=For(x,lambda x:intro(App(S,x),incoming))
                    return ei(Ex(t,apps(D,y,t)),t,cproof(sy,st,ryt,inc))
                return unpack(mp(spec(RS,z),jz),att)
            return unpack(got,atz)
        Succ=For(y,lambda y:intro(App(U,y),succu))
        removed=use(remove_layer,[R,J,S,U],[TW,NS,RS,US,Succ])
        VS,NV,RV=[proj(removed,j,3) for j in range(3)]
        x=fresh(X,'x');Vv=Lam(x,And(App(S,x),Not(App(U,x))))
        VJ=use(subset_trans,[Vv,S,J],[VS,SJ])
        bound=For(x,lambda x:intro(App(Vv,x),lambda h:by_contra(App(Hq,x),lambda nx:mp(ar(h),ai(al(h),nx)))))
        y=fresh(X,'y');z=fresh(X,'z')
        routeV=gens([x,y,z],intro(App(Vv,x),lambda vx:intro(App(Vv,y),lambda vy:intro(apps(R,x,y),lambda rxy:intro(apps(B,y,z),lambda byz:apply(spec(Route,x,y,z),al(vx),al(vy),rxy,byz))))))
        cleared=apply(spec(IH,Vv),VJ,NV,RV,routeV,bound)
        def clearU(W,h):
            WV,NW,RW,NB=[proj(h,j,4) for j in range(4)]
            return ei(Clear(R,B,J,S),W,cproof(use(subset_trans,[W,Vv,S],[WV,VS]),NW,RW,NB))
        answer=unpack(cleared,clearU)
        return ai(closednext,gens([S],iis(hs,answer)))
    step_proof=For(Q,lambda Q:intro(property(Q),step))
    q=fresh(Arr(X,O),'Q')
    induction=apply(spec(hyp(HeightProfile(B,H)),Lam(q,property(q))),base,step_proof)
    return lemma('finite_height_profile_elimination',induction,[R,B,J,H],glob+[HeightProfile(B,H)])
profile_elim=make_uniform_stage()


def make_uniform_clear():
    R=fresh(Rel(X),'R');B=fresh(Rel(X),'B');J=fresh(Arr(X,O),'J');S=fresh(Arr(X,O),'S')
    ass=[TransWF(R),SubRel(B,R),domain(R,J),Sub(S,J),NE(S),Rep(R,J,S),LocalRoute(R,B,S),Bounded(B,S)]
    h=list(map(hyp,ass))
    def atH(H,bound):
        stage=ar(use(profile_elim,[R,B,J,H],h[:3]+[al(bound)]))
        return apply(spec(stage,S),*h[3:7],ar(bound))
    return lemma('uniform_height_representative_elimination',unpack(h[-1],atH),[R,B,J,S],ass)
uniform_clear=make_uniform_clear()


def make_pointwise_clear():
    R=fresh(Rel(X),'R');B=fresh(Rel(X),'B');J=fresh(Arr(X,O),'J');S=fresh(Arr(X,O),'S')
    ass=[TransWF(R),SubRel(B,R),domain(R,J),Sub(S,J),NE(S),Rep(R,J,S),StrongRoute(R,B,S),PointwiseBounded(B,S)]
    TW,BR,DJ,SJ,NS,RS,Route,PW=map(hyp,ass)
    def at_a(a,sa):
        def at_H(H,hh):
            PH,Ha=al(hh),ar(hh)
            data=use(profile_elim,[R,B,J,H],[TW,BR,DJ,PH]);closed=al(data)
            x=fresh(X,'x');L=Lam(x,And(App(S,x),App(Next(B,H),x)))
            LS=For(x,lambda x:intro(App(L,x),lambda h:al(h)))
            NL=ei(NE(L),a,ai(sa,Ha))
            def nonincrease(x,y,sx,sy,rxy,hx):
                z=fresh(X,'z')
                def edge(yz):
                    pxz=apply(spec(Route,x,y,z),sx,sy,rxy,yz)
                    return unpack(pxz,lambda u,hu:use(star_forward,[B,H,u,z],[closed,ar(hu),mp(spec(hx,u),al(hu))]))
                return For(z,lambda z:intro(apps(B,y,z),edge))
            z=fresh(X,'z');x=fresh(X,'x')
            def repz(jz):
                incoming=Ex(x,And(App(L,x),apps(R,x,z)))
                def yes(ein):
                    def at_t(t,ht):
                        ht_bound=unpack(ein,lambda x,h:nonincrease(x,t,al(al(h)),al(ht),apply(spec(ar(ht),x),al(al(h)),ar(h)),ar(al(h))))
                        restricted=For(x,lambda x:intro(App(L,x),lambda lx:intro(apps(R,x,z),lambda rxz:apply(spec(ar(ht),x),al(lx),rxz))))
                        return ei(rep_target(R,J,L,z),t,ai(ai(al(ht),ht_bound),restricted))
                    return unpack(mp(spec(RS,z),jz),at_t)
                def no(nin):
                    vac=For(x,lambda x:intro(App(L,x),lambda lx:intro(apps(R,x,z),lambda rxz:absurd(mp(nin,ei(incoming,x,ai(lx,rxz))),apps(R,x,a)))))
                    return ei(rep_target(R,J,L,z),a,ai(ai(sa,Ha),vac))
                return cases(em(incoming),yes,no)
            RL=For(z,lambda z:intro(App(J,z),repz))
            y=fresh(X,'y');z=fresh(X,'z')
            routeL=gens([x,y,z],intro(App(L,x),lambda lx:intro(App(L,y),lambda ly:intro(apps(R,x,y),lambda e:intro(apps(B,y,z),lambda b:ol(apply(spec(Route,x,y,z),al(lx),al(ly),e,b),apps(R,x,z)))))))
            bound=For(x,lambda x:intro(App(L,x),lambda h:ar(h)))
            cleared=apply(spec(ar(data),L),use(subset_trans,[L,S,J],[LS,SJ]),NL,RL,routeL,bound)
            def atU(U,hu):
                UL,NU,RU,NB=[proj(hu,j,4) for j in range(4)]
                return ei(Clear(R,B,J,S),U,cproof(use(subset_trans,[U,L,S],[UL,LS]),NU,RU,NB))
            return unpack(cleared,atU)
        return unpack(mp(spec(PW,a),sa),at_H)
    return lemma('pointwise_height_representative_elimination',unpack(NS,at_a),[R,B,J,S],ass)
pointwise_clear=make_pointwise_clear()


# Abstract ordinal interface. It is specialized mathematically to any ordinal
# containing the ranks. The order and rank hypotheses remain explicit.
Ord='Ord'
def LE(L,a,b):return Not(apps(L,b,a))
def Rev(L):
    a=fresh(type_of(L)[1],'a');b=fresh(type_of(a),'b')
    return Lam(a,Lam(b,apps(L,b,a)))
def RankDecrease(B,L,rho):
    x=fresh(X,'x');y=fresh(X,'y')
    return alls([x,y],Imp(apps(B,x,y),apps(L,App(rho,y),App(rho,x))))
def RankLub(B,L,rho):
    x=fresh(X,'x');a=fresh(Ord,'alpha');y=fresh(X,'y')
    return alls([x,a],Imp(All(y,Imp(apps(B,x,y),apps(L,App(rho,y),a))),LE(L,App(rho,x),a)))
def SuccRank(L,b,a):
    c=fresh(Ord,'gamma')
    return And(apps(L,b,a),All(c,Imp(apps(L,c,a),Not(apps(L,b,c)))))
def ZeroRank(L,a):
    b=fresh(Ord,'beta');return All(b,Not(apps(L,b,a)))
def LimitRank(L,a):
    b=fresh(Ord,'beta');return And(Not(ZeroRank(L,a)),Not(Ex(b,SuccRank(L,b,a))))
def MinimumRank(L,rho,S,a):
    x=fresh(X,'x');return And(App(S,a),All(x,Imp(App(S,x),LE(L,App(rho,a),App(rho,x)))))
def RankLayer(rho,S,a):
    x=fresh(X,'x');return Lam(x,And(App(S,x),Eq(App(rho,x),a)))

def make_order_helpers():
    L=fresh(Rel(Ord),'L');a=fresh(Ord,'a');b=fresh(Ord,'b');c=fresh(Ord,'c')
    ass=[tri(L),LE(L,a,b),LE(L,b,a)]
    triL,ab,ba=map(hyp,ass)
    eq=cases(spec(triL,a,b),lambda e:e,lambda h:cases(h,lambda e:absurd(mp(ba,e),Eq(a,b)),lambda e:absurd(mp(ab,e),Eq(a,b))))
    anti=lemma('rank_order_antisymmetry',eq,[L,a,b],ass)
    ass=[tri(L),trans(L),apps(L,a,b),LE(L,b,c)]
    trich,tr,L_ab,bc=map(hyp,ass);v=fresh(Ord,'v')
    out=cases(spec(trich,b,c),lambda eq:eq_transport(eq,Lam(v,apps(L,a,v)),L_ab),lambda h:cases(h,lambda lbc:apply(spec(tr,a,b,c),L_ab,lbc),lambda lcb:absurd(mp(bc,lcb),apps(L,a,c))))
    ltle=lemma('rank_strict_then_nonstrict',out,[L,a,b,c],ass)
    return anti,ltle
rank_antisym,rank_ltle=make_order_helpers()


def make_rank_path():
    B=fresh(Rel(X),'B');L=fresh(Rel(Ord),'L');rho=fresh(Arr(X,Ord),'rank');x=fresh(X,'x');z=fresh(X,'z')
    ass=[trans(L),RankDecrease(B,L,rho),Plus(B,x,z)]
    tr,dec,path=map(hyp,ass)
    def at_u(u,hu):
        v=fresh(X,'v');w=fresh(X,'w');pred=Lam(v,apps(L,App(rho,v),App(rho,x)))
        step=gens([v,w],intro(apps(B,v,w),lambda e:intro(App(pred,v),lambda lv:apply(spec(tr,App(rho,w),App(rho,v),App(rho,x)),mp(spec(dec,v,w),e),lv))))
        return use(star_forward,[B,pred,u,z],[step,ar(hu),mp(spec(dec,x,u),al(hu))])
    return lemma('positive_paths_strictly_decrease_rank',unpack(path,at_u),[B,L,rho,x,z],ass)
rank_path=make_rank_path()


def make_rank_nonincrease():
    R=fresh(Rel(X),'R');B=fresh(Rel(X),'B');S=fresh(Arr(X,O),'S');L=fresh(Rel(Ord),'L');rho=fresh(Arr(X,Ord),'rank');x=fresh(X,'x');y=fresh(X,'y');z=fresh(X,'z')
    ass=[trans(L),RankDecrease(B,L,rho),RankLub(B,L,rho),StrongRoute(R,B,S),App(S,x),App(S,y),apps(R,x,y)]
    tr,dec,lub,route,sx,sy,rxy=map(hyp,ass)
    small=For(z,lambda z:intro(apps(B,y,z),lambda e:use(rank_path,[B,L,rho,x,z],[tr,dec,apply(spec(route,x,y,z),sx,sy,rxy,e)])))
    out=mp(spec(lub,y,App(rho,x)),small)
    return lemma('shortened_rerouting_does_not_increase_rank',out,[R,B,S,L,rho,x,y],ass)
rank_nonincrease=make_rank_nonincrease()


def make_successor_attained():
    B=fresh(Rel(X),'B');L=fresh(Rel(Ord),'L');rho=fresh(Arr(X,Ord),'rank');y=fresh(X,'y');beta=fresh(Ord,'beta');alpha=fresh(Ord,'alpha');z=fresh(X,'z')
    ass=[tri(L),RankDecrease(B,L,rho),RankLub(B,L,rho),Eq(App(rho,y),alpha),SuccRank(L,beta,alpha)]
    trich,dec,lub,eqy,succ=map(hyp,ass)
    out=Ex(z,And(apps(B,y,z),Eq(App(rho,z),beta)))
    def notfound(nf):
        def atz(e):
            v=fresh(Ord,'v');small=eq_transport(eqy,Lam(v,apps(L,App(rho,z),v)),mp(spec(dec,y,z),e))
            nb=mp(spec(ar(succ),App(rho,z)),small)
            return cases(spec(trich,App(rho,z),beta),lambda eq:absurd(mp(nf,ei(out,z,ai(e,eq))),apps(L,App(rho,z),beta)),lambda h:cases(h,lambda lt:lt,lambda gt:absurd(mp(nb,gt),apps(L,App(rho,z),beta))))
        strict=For(z,lambda z:intro(apps(B,y,z),atz))
        le=mp(spec(lub,y,beta),strict)
        v=fresh(Ord,'v');lealpha=eq_transport(eqy,Lam(v,LE(L,v,beta)),le)
        return mp(lealpha,al(succ))
    return lemma('successor_rank_has_predecessor_rank_successor',by_contra(out,notfound),[B,L,rho,y,beta,alpha],ass)
successor_attained=make_successor_attained()


def make_successor_path_one():
    B=fresh(Rel(X),'B');L=fresh(Rel(Ord),'L');rho=fresh(Arr(X,Ord),'rank');x=fresh(X,'x');z=fresh(X,'z');beta=fresh(Ord,'beta');alpha=fresh(Ord,'alpha')
    ass=[tri(L),trans(L),RankDecrease(B,L,rho),SuccRank(L,beta,alpha),LE(L,App(rho,x),alpha),Eq(App(rho,z),beta),Plus(B,x,z)]
    trich,tr,dec,succ,bound,eqz,pxz=map(hyp,ass)
    def first(u,hu):
        def eqcase(eq):
            v=fresh(X,'v');return eq_transport(eq,Lam(v,apps(B,x,v)),al(hu))
        def pos(puz):
            z_u=use(rank_path,[B,L,rho,u,z],[tr,dec,puz])
            v=fresh(Ord,'v');beta_u=eq_transport(eqz,Lam(v,apps(L,v,App(rho,u))),z_u)
            ualpha=use(rank_ltle,[L,App(rho,u),App(rho,x),alpha],[trich,tr,mp(spec(dec,x,u),al(hu)),bound])
            contradiction=mp(mp(spec(ar(succ),App(rho,u)),ualpha),beta_u)
            return absurd(contradiction,apps(B,x,z))
        return cases(use(star_split,[B,u,z],[ar(hu)]),eqcase,pos)
    return lemma('path_into_predecessor_rank_is_one_edge',unpack(pxz,first),[B,L,rho,x,z,beta,alpha],ass)
successor_path_one=make_successor_path_one()


def make_successor_layer():
    R=fresh(Rel(X),'R');B=fresh(Rel(X),'B');J=fresh(Arr(X,O),'J');S=fresh(Arr(X,O),'S');L=fresh(Rel(Ord),'L');rho=fresh(Arr(X,Ord),'rank');beta=fresh(Ord,'beta');alpha=fresh(Ord,'alpha')
    x=fresh(X,'x');upper=All(x,Imp(App(S,x),LE(L,App(rho,x),alpha)))
    ass=[TransWF(R),SubRel(B,R),domain(R,J),NE(S),Rep(R,J,S),LocalRoute(R,B,S),tri(L),trans(L),RankDecrease(B,L,rho),RankLub(B,L,rho),SuccRank(L,beta,alpha),upper]
    TW,BR,DJ,NS,RS,Route,trich,tr,dec,lub,succ,Bound=map(hyp,ass)
    U=RankLayer(rho,S,alpha);D=Dominate(R,S);y=fresh(X,'y');t=fresh(X,'t')
    US=For(x,lambda x:intro(App(U,x),lambda h:al(h)))
    def sy(uy):
        sy,eqy=al(uy),ar(uy)
        got=use(successor_attained,[B,L,rho,y,beta,alpha],[trich,dec,lub,eqy,succ])
        def atz(z,hz):
            byz,eqz=al(hz),ar(hz)
            jz=ar(mp(spec(DJ,y,z),mp(spec(BR,y,z),byz)))
            def att(t,ht):
                st,rep=al(ht),ar(ht);ryt=apply(spec(rep,y),sy,mp(spec(BR,y,z),byz))
                def inx(sx):
                    def rx(rxy):
                        r=apply(spec(Route,x,y,z),sx,sy,rxy,byz)
                        bxz=lambda p:mp(spec(BR,x,z),use(successor_path_one,[B,L,rho,x,z,beta,alpha],[trich,tr,dec,succ,mp(spec(Bound,x),sx),eqz,p]))
                        rxz=cases(r,bxz,lambda e:e)
                        return apply(spec(rep,x),sx,rxz)
                    return intro(apps(R,x,y),rx)
                inc=For(x,lambda x:intro(App(S,x),inx))
                return ei(Ex(t,apps(D,y,t)),t,cproof(sy,st,ryt,inc))
            return unpack(mp(spec(RS,z),jz),att)
        return unpack(got,atz)
    Succ=For(y,lambda y:intro(App(U,y),sy))
    out=use(remove_layer,[R,J,S,U],[TW,NS,RS,US,Succ])
    return lemma('successor_ordinal_layer_elimination',out,[R,B,J,S,L,rho,beta,alpha],ass)
successor_layer=make_successor_layer()


def make_minimum_stratum_rep():
    R=fresh(Rel(X),'R');B=fresh(Rel(X),'B');J=fresh(Arr(X,O),'J');S=fresh(Arr(X,O),'S');L=fresh(Rel(Ord),'L');rho=fresh(Arr(X,Ord),'rank');a=fresh(X,'a')
    ass=[Rep(R,J,S),StrongRoute(R,B,S),tri(L),trans(L),RankDecrease(B,L,rho),RankLub(B,L,rho),MinimumRank(L,rho,S,a)]
    RS,Route,trich,tr,dec,lub,Min=map(hyp,ass);sa=al(Min);mn=ar(Min);alpha=App(rho,a)
    U=RankLayer(rho,S,alpha);x=fresh(X,'x');z=fresh(X,'z')
    NU=ei(NE(U),a,ai(sa,refl(alpha)))
    def repz(jz):
        incoming=Ex(x,And(App(U,x),apps(R,x,z)))
        def yes(ein):
            def at_t(t,ht):
                st,rep=al(ht),ar(ht)
                def incomingx(x,h):
                    ux,rxz=al(h),ar(h);sx=al(ux);eqx=ar(ux)
                    rxt=apply(spec(rep,x),sx,rxz)
                    le=use(rank_nonincrease,[R,B,S,L,rho,x,t],[tr,dec,lub,Route,sx,st,rxt])
                    v=fresh(Ord,'v');talpha=eq_transport(eqx,Lam(v,LE(L,App(rho,t),v)),le)
                    return use(rank_antisym,[L,App(rho,t),alpha],[trich,talpha,mp(spec(mn,t),st)])
                eqt=unpack(ein,incomingx)
                rp=For(x,lambda x:intro(App(U,x),lambda ux:intro(apps(R,x,z),lambda rxz:apply(spec(rep,x),al(ux),rxz))))
                return ei(rep_target(R,J,U,z),t,ai(ai(st,eqt),rp))
            return unpack(mp(spec(RS,z),jz),at_t)
        def no(nin):
            rp=For(x,lambda x:intro(App(U,x),lambda ux:intro(apps(R,x,z),lambda rxz:absurd(mp(nin,ei(incoming,x,ai(ux,rxz))),apps(R,x,a)))))
            return ei(rep_target(R,J,U,z),a,ai(ai(sa,refl(alpha)),rp))
        return cases(em(incoming),yes,no)
    RU=For(z,lambda z:intro(App(J,z),repz))
    return lemma('minimum_rank_stratum_has_representatives',ai(NU,RU),[R,B,J,S,L,rho,a],ass)
minimum_rep=make_minimum_stratum_rep()


def make_minimum_not_successor():
    R=fresh(Rel(X),'R');B=fresh(Rel(X),'B');J=fresh(Arr(X,O),'J');S=fresh(Arr(X,O),'S');L=fresh(Rel(Ord),'L');rho=fresh(Arr(X,Ord),'rank');a=fresh(X,'a');beta=fresh(Ord,'beta')
    ass=[TransWF(R),SubRel(B,R),domain(R,J),Rep(R,J,S),StrongRoute(R,B,S),irrefl(L),tri(L),trans(L),RankDecrease(B,L,rho),RankLub(B,L,rho),MinimumRank(L,rho,S,a)]
    TW,BR,DJ,RS,Route,IR,trich,tr,dec,lub,Min=map(hyp,ass)
    alpha=App(rho,a);U=RankLayer(rho,S,alpha);x=fresh(X,'x');y=fresh(X,'y');z=fresh(X,'z')
    nr=use(minimum_rep,[R,B,J,S,L,rho,a],[RS,Route,trich,tr,dec,lub,Min]);NU,RU=al(nr),ar(nr)
    routeU=gens([x,y,z],intro(App(U,x),lambda ux:intro(App(U,y),lambda uy:intro(apps(R,x,y),lambda e:intro(apps(B,y,z),lambda b:ol(apply(spec(Route,x,y,z),al(ux),al(uy),e,b),apps(R,x,z)))))))
    def upper(ux):
        v=fresh(Ord,'v');return eq_transport(use(inst(eq_sym,X=Ord),[App(rho,x),alpha],[ar(ux)]),Lam(v,LE(L,v,alpha)),spec(IR,alpha))
    Bound=For(x,lambda x:intro(App(U,x),upper))
    out=Not(Ex(beta,SuccRank(L,beta,alpha)))
    def exsucc(es):
        def atb(b,succ):
            removed=use(successor_layer,[R,B,J,U,L,rho,b,alpha],[TW,BR,DJ,NU,RU,routeU,trich,tr,dec,lub,succ,Bound])
            nonempty=proj(removed,1,3)
            return unpack(nonempty,lambda x,h:mp(ar(h),ai(al(h),ar(al(h)))))
        return unpack(es,atb)
    return lemma('minimum_layer_rank_is_not_a_successor',intro(norm(out)[1],exsucc),[R,B,J,S,L,rho,a],ass)
minimum_not_successor=make_minimum_not_successor()


def make_rank_minimum_exists():
    L=fresh(Rel(Ord),'L');rho=fresh(Arr(X,Ord),'rank');S=fresh(Arr(X,O),'S');x=fresh(X,'x');a=fresh(Ord,'alpha');b=fresh(Ord,'beta')
    ass=[WF(Rev(L)),NE(S)];W,NS=map(hyp,ass)
    Im=Lam(a,Ex(x,And(App(S,x),Eq(App(rho,x),a))))
    NI=unpack(NS,lambda x,sx:ei(NE(Im),App(rho,x),ei(norm(App(Im,App(rho,x))),x,ai(sx,refl(App(rho,x))))))
    minim=use(inst(wf_minimum,X=Ord),[Rev(L),Im],[W,NI])
    def atalpha(alpha,ha):
        def ata(a,h):
            sa,eqa=al(h),ar(h)
            def atx(sx):
                mem=ei(norm(App(Im,App(rho,x))),x,ai(sx,refl(App(rho,x))))
                no= intro(apps(L,App(rho,x),alpha),lambda e:apply(spec(ar(ha),App(rho,x)),e,mem))
                v=fresh(Ord,'v');reverse=use(inst(eq_sym,X=Ord),[App(rho,a),alpha],[eqa])
                return eq_transport(reverse,Lam(v,LE(L,v,App(rho,x))),no)
            minimal=ai(sa,For(x,lambda x:intro(App(S,x),atx)))
            w=fresh(X,'a');return ei(Ex(w,MinimumRank(L,rho,S,w)),a,minimal)
        return unpack(al(ha),ata)
    return lemma('well_ordered_ranks_attain_a_minimum',unpack(minim,atalpha),[L,rho,S],ass)
rank_minimum=make_rank_minimum_exists()


# A stage oracle abstracts the elimination mechanism; the family proof uses
# only this interface, not a finiteness or height assumption on the carrier.
def Minima(F,J,zero):
    x=fresh(X,'x');return Lam(x,And(App(J,x),No(App(F,zero),x)))
def Stages(F,Orel,zero,pen,J):
    i=fresh(Idx,'i');S=fresh(Arr(X,O),'S');R=Total(F);M=Minima(F,J,zero)
    return alls([i,S],imps([Not(Eq(i,zero)),apps(Orel,i,pen),Sub(S,M),NE(S),Rep(R,J,S),NoFrom(Part(F,Orel,i,True),S)],Clear(R,App(F,i),J,S)))

def make_family_stage_core():
    F=fresh(FamTy,'F');Orel=fresh(Rel(Idx),'order');zero=fresh(Idx,'zero');pen=fresh(Idx,'pen');last=fresh(Idx,'last')
    J=fresh(Arr(X,O),'J');CK=fresh(Arr(Idx,O),'coverK');R=Total(F);A=App(F,zero)
    x=fresh(X,'x');M=Lam(x,And(App(J,x),No(A,x)));i=fresh(Idx,'i')
    allK=All(i,App(CK,i))
    ass=[Fin(CK),allK,irrefl(Orel),trans(Orel),tri(Orel),least(Orel,zero),LastPair(Orel,pen,last),WFcolors(F),Gzero(F,Orel,zero),Gothers(F,Orel,zero),Stages(F,Orel,zero,pen,J),domain(R,J),NE(J),serial(R,J)]
    FK,AK,OI,OT,OTT,LZ,LP,WFC,G0,Gi,IB,DJ,NJ,SJ=map(hyp,ass)
    irR=use(union_irrefl,[F],[WFC])
    NM=use(init_nonempty,[F,zero,J],[WFC,DJ,NJ])
    RM=use(init_rep,[F,Orel,zero,J],[WFC,LZ,G0,DJ])
    Vv=fresh(Arr(Idx,O),'V');S=fresh(Arr(X,O),'S')
    def good(Vv):return Ex(S,CAnd(Sub(S,M),NE(S),Rep(R,J,S),CoversActive(F,S,Vv)))
    G=Lam(Vv,good(Vv))
    i=fresh(Idx,'i');x=fresh(X,'x');z=fresh(X,'z')
    covM=gens([i,x,z],iis([App(M,x),apps(F,i,x,z)],spec(AK,i)))
    goodM=ei(good(CK),M,cproof(spec(subset_refl,M),NM,RM,covM))
    candidate=ei(candidate_ex(G,CK),CK,ai(spec(inst(subset_refl,X=Idx),CK),goodM))
    minima=mp(spec(mp(spec(inst(finite_minimal_subset,X=Idx),CK),FK),G),candidate)
    def atV(Vv,hV):
        vmin=ar(ar(hV));witness=al(ar(hV))
        def atS(S,hS):
            SM,NS,RS,Cov=[proj(hS,i,4) for i in range(4)]
            def sj(x,sx):return al(mp(spec(SM,x),sx))
            def sn(x,sx):return ar(mp(spec(SM,x),sx))
            def one_active(x,sx):
                return unpack(mp(spec(SJ,x),sj(x,sx)),lambda y,h:unpack(ar(h),lambda i,e:ei(NE(Active(F,S)),i,active_member(F,S,i,x,y,sx,e))))
            na=unpack(NS,one_active)
            j=fresh(Idx,'j');ac=For(j,lambda j:intro(App(Active(F,S),j),lambda _:spec(AK,j)))
            minidx=apply(spec(apply(spec(inst(finite_source,X=Idx),Orel,CK),OI,OT,FK),Active(F,S)),ac,na)
            def ati(i,hi):
                acti=al(hi);imin=ar(hi);B=App(F,i)
                def block(j,x,y,before,sx,e):
                    return mp(mp(spec(imin,j),active_member(F,S,j,x,y,sx,e)),before)
                def blockp(x,y,sx,prior):
                    return unpack(prior,lambda j,h:block(j,x,y,al(h),sx,ar(h)))
                def notzero(eq):
                    k=fresh(Idx,'k')
                    return unpack(acti,lambda x,hx:unpack(hx,lambda z,h:mp(spec(sn(x,al(h)),z),eq_transport(eq,Lam(k,apps(F,k,x,z)),ar(h)))))
                nz=intro(Eq(i,zero),notzero)
                x=fresh(X,'x');z=fresh(X,'z')
                NoPrior=For(x,lambda x:intro(App(S,x),lambda sx:For(z,lambda z:intro(apps(Part(F,Orel,i,True),x,z),lambda p:blockp(x,z,sx,p)))))
                # Representatives imply seriality on the current S.
                def rserial(sx):
                    def atz(z,hz):
                        def att(t,ht):
                            return ei(serial_target(R,S,x),t,ai(al(ht),apply(spec(ar(ht),x),sx,ar(hz))))
                        return unpack(mp(spec(RS,z),al(hz)),att)
                    return unpack(mp(spec(SJ,x),sj(x,sx)),atz)
                sR=For(x,lambda x:intro(App(S,x),rserial))
                def last_case(eqlast):
                    # All current outgoing edges must have the greatest color.
                    x=fresh(X,'x');y=fresh(X,'y');k=fresh(Idx,'k')
                    def sx(sx):
                        def aty(y,hy):
                            def atj(j,edge):
                                def eql(eq):return eq_transport(eq,Lam(k,apps(F,k,x,y)),edge)
                                def rest(h):
                                    def eqp(eq):
                                        # j=pen, i=last: transport pen<last to j<i.
                                        revj=use(inst(eq_sym,X=Idx),[j,pen],[eq])
                                        revi=use(inst(eq_sym,X=Idx),[i,last],[eqlast])
                                        ji=eq_transport(revj,Lam(k,apps(Orel,k,last)),al(LP))
                                        ji=eq_transport(revi,Lam(k,apps(Orel,j,k)),ji)
                                        return absurd(block(j,x,y,ji,sx,edge),apps(F,last,x,y))
                                    def jp(jp):
                                        jl=apply(spec(OT,j,pen,last),jp,al(LP))
                                        revi=use(inst(eq_sym,X=Idx),[i,last],[eqlast])
                                        ji=eq_transport(revi,Lam(k,apps(Orel,j,k)),jl)
                                        return absurd(block(j,x,y,ji,sx,edge),apps(F,last,x,y))
                                    return cases(h,eqp,jp)
                                return cases(spec(ar(LP),j),eql,rest)
                            e=unpack(ar(hy),atj)
                            return ei(serial_target(App(F,last),S,x),y,ai(al(hy),e))
                        return unpack(mp(spec(sR,x),sx),aty)
                    sLast=For(x,lambda x:intro(App(S,x),sx))
                    return use(wf_no_serial,[App(F,last),S],[spec(WFC,last),NS,sLast])
                def pen_case(eqpen):
                    P0=App(F,pen);Q=App(F,last);Earlier=Part(F,Orel,pen,True);k=fresh(Idx,'k')
                    noP=eq_transport(eqpen,Lam(k,NoFrom(Part(F,Orel,k,True),S)),NoPrior)
                    penNZ=eq_transport(eqpen,Lam(k,Not(Eq(k,zero))),nz)
                    x=fresh(X,'x');y=fresh(X,'y');z=fresh(X,'z')
                    def qroute(qxy):
                        def proute(pyz):
                            tail=ei(norm(apps(Part(F,Orel,pen),x,y)),last,ai(al(LP),qxy))
                            r=apply(spec(Gi,pen,x,y,z),penNZ,tail,pyz)
                            def other(h):
                                return cases(h,lambda p:ol(p,apps(Q,x,z)),lambda t:ore(use(tail_pair_exact,[F,Orel,pen,last,x,z],[OI,OT,LP,t]),Plus(P0,x,z)))
                            return cases(r,lambda d:ol(d,Or(Plus(P0,x,z),apps(Q,x,z))),lambda h:ore(other(h),Detour(Earlier,R,x,z)))
                        return intro(apps(P0,y,z),proute)
                    route=gens([x,y,z],intro(apps(Q,x,y),qroute))
                    def sx(sx):
                        def aty(y,hy):
                            def atj(j,edge):
                                def islast(eq):return ore(eq_transport(eq,Lam(k,apps(F,k,x,y)),edge),apps(P0,x,y))
                                def rest(h):
                                    def ispen(eq):return ol(eq_transport(eq,Lam(k,apps(F,k,x,y)),edge),apps(Q,x,y))
                                    def before(jp):
                                        prior=ei(norm(apps(Earlier,x,y)),j,ai(jp,edge))
                                        return absurd(mp(spec(mp(spec(noP,x),sx),y),prior),apps(Cup(P0,Q),x,y))
                                    return cases(h,ispen,before)
                                return cases(spec(ar(LP),j),islast,rest)
                            e=unpack(ar(hy),atj)
                            return ei(serial_target(Cup(P0,Q),S,x),y,ai(al(hy),e))
                        return unpack(mp(spec(sR,x),sx),aty)
                    ss=For(x,lambda x:intro(App(S,x),sx))
                    return use(final_pair,[P0,Q,Earlier,R,S],[spec(WFC,pen),spec(WFC,last),route,noP,NS,ss])
                def internal_case(ipen):
                    cleared=apply(spec(IB,i,S),nz,ipen,SM,NS,RS,NoPrior)
                    def atU(U,hu):
                        US,NU,RU,NoB=[proj(hu,j,4) for j in range(4)]
                        UM=use(subset_trans,[U,S,M],[US,SM]);Vp=Del(Vv,i)
                        j=fresh(Idx,'j');x=fresh(X,'x');y=fresh(X,'y');k=fresh(Idx,'k')
                        def covered(ux):
                            def edge(e):
                                vj=apply(spec(Cov,j,x,y),mp(spec(US,x),ux),e)
                                neq=intro(Eq(j,i),lambda eq:mp(spec(mp(spec(NoB,x),ux),y),eq_transport(eq,Lam(k,apps(F,k,x,y)),e)))
                                return ai(vj,neq)
                            return intro(apps(F,j,x,y),edge)
                        cov=gens([j,x,y],intro(App(U,x),covered))
                        gvp=ei(good(Vp),U,cproof(UM,NU,RU,cov))
                        j=fresh(Idx,'j');vpv=For(j,lambda j:intro(App(Vp,j),lambda h:al(h)))
                        vvp=apply(spec(vmin,Vp),vpv,gvp)
                        vi=unpack(acti,lambda x,hx:unpack(hx,lambda y,h:apply(spec(Cov,i,x,y),al(h),ar(h))))
                        return mp(ar(mp(spec(vvp,i),vi)),refl(i))
                    return unpack(cleared,atU)
                return cases(spec(ar(LP),i),last_case,lambda h:cases(h,pen_case,internal_case))
            return unpack(minidx,ati)
        return unpack(witness,atS)
    return lemma('serial_domain_with_eliminable_internal_stages_impossible',unpack(minima,atV),[F,Orel,zero,pen,last,J,CK],ass)
stage_core=make_family_stage_core()


def make_stage_route(strong=False):
    F=fresh(FamTy,'F');Orel=fresh(Rel(Idx),'order');zero=fresh(Idx,'zero');i=fresh(Idx,'i');S=fresh(Arr(X,O),'S')
    R=Total(F);B=App(F,i);P0=Part(F,Orel,i,True)
    ass=[tri(Orel),NoFrom(P0,S),Short(F,Orel,i) if strong else Gothers(F,Orel,zero),Not(Eq(i,zero))]
    TT,NoP,Route,NZ=map(hyp,ass)
    x=fresh(X,'x');y=fresh(X,'y');z=fresh(X,'z');k=fresh(Idx,'k')
    conclusion=Plus(B,x,z) if strong else Or(Plus(B,x,z),apps(R,x,z))
    def sx(sx):
        def sy(sy):
            def rx(rxy):
                def bz(byz):
                    def atj(j,e):
                        def equal(eq):
                            bxy=eq_transport(eq,Lam(k,apps(F,k,x,y)),e)
                            p=use(plus_cons,[B,x,y,z],[bxy,use(plus_one,[B,y,z],[byz])])
                            return p if strong else ol(p,apps(R,x,z))
                        def other(h):
                            def before(ji):
                                prior=ei(norm(apps(P0,x,y)),j,ai(ji,e))
                                return absurd(mp(spec(mp(spec(NoP,x),sx),y),prior),conclusion)
                            def later(ij):
                                tail=ei(norm(apps(Part(F,Orel,i),x,y)),j,ai(ij,e))
                                routed=apply(spec(Route,x,y,z),tail,byz) if strong else apply(spec(Route,i,x,y,z),NZ,tail,byz)
                                def det(d):return unpack(d,lambda u,h:absurd(mp(spec(mp(spec(NoP,x),sx),u),al(h)),conclusion))
                                def rest(hh):
                                    if strong:return hh
                                    return cases(hh,lambda p:ol(p,apps(R,x,z)),lambda t:ore(use(tail_total,[F,Orel,i,x,z],[t]),Plus(B,x,z)))
                                return cases(routed,det,rest)
                            return cases(h,before,later)
                        return cases(spec(TT,j,i),equal,other)
                    return unpack(rxy,atj)
                return intro(apps(B,y,z),bz)
            return intro(apps(R,x,y),rx)
        return intro(App(S,y),sy)
    p=gens([x,y,z],intro(App(S,x),sx))
    return lemma('earlier_free_stage_'+('strong' if strong else 'full')+'_rerouting',p,[F,Orel,zero,i,S],ass)
full_stage_route=make_stage_route(False)
strong_stage_route=make_stage_route(True)


def MixedHeights(F,Orel,zero,pen,M):
    i=fresh(Idx,'i');B=App(F,i)
    return All(i,imps([Not(Eq(i,zero)),apps(Orel,i,pen)],Or(Bounded(B,M),And(Short(F,Orel,i),PointwiseBounded(B,M)))))

def make_mixed_stages():
    F=fresh(FamTy,'F');Orel=fresh(Rel(Idx),'order');zero=fresh(Idx,'zero');pen=fresh(Idx,'pen');J=fresh(Arr(X,O),'J');C=fresh(Arr(Idx,O),'coverK');R=Total(F);M=Minima(F,J,zero);i=fresh(Idx,'i')
    ass=[WFcolors(F),Fin(C),All(i,App(C,i)),tri(Orel),Gothers(F,Orel,zero),domain(R,J),MixedHeights(F,Orel,zero,pen,M)]
    WFC,FCc,AC,TT,GI,DJ,Mix=map(hyp,ass)
    TW=use(family_transwf,[F,C],[WFC,FCc,AC]);S=fresh(Arr(X,O),'S')
    premises=[Not(Eq(i,zero)),apps(Orel,i,pen),Sub(S,M),NE(S),Rep(R,J,S),NoFrom(Part(F,Orel,i,True),S)]
    NZ,IP,SM,NS,RS,NP=map(hyp,premises);B=App(F,i)
    x=fresh(X,'x');y=fresh(X,'y')
    SJ=For(x,lambda x:intro(App(S,x),lambda sx:al(mp(spec(SM,x),sx))))
    BR=gens([x,y],intro(apps(B,x,y),lambda e:use(color_total,[F,i,x,y],[e])))
    data=apply(spec(Mix,i),NZ,IP)
    def uniform(b):
        def atH(H,h):
            bound=use(subset_trans,[S,M,Next(B,H)],[SM,ar(h)])
            Hb=ei(Bounded(B,S),H,ai(al(h),bound))
            route=use(full_stage_route,[F,Orel,zero,i,S],[TT,NP,GI,NZ])
            return use(uniform_clear,[R,B,J,S],[TW,BR,DJ,SJ,NS,RS,route,Hb])
        return unpack(b,atH)
    def pointwise(h):
        route=use(strong_stage_route,[F,Orel,zero,i,S],[TT,NP,al(h),NZ])
        pw=For(x,lambda x:intro(App(S,x),lambda sx:mp(spec(ar(h),x),mp(spec(SM,x),sx))))
        return use(pointwise_clear,[R,B,J,S],[TW,BR,DJ,SJ,NS,RS,route,pw])
    out=cases(data,uniform,pointwise)
    return lemma('mixed_height_bounds_eliminate_each_internal_stage',gens([i,S],iis(premises,out)),[F,Orel,zero,pen,J,C],ass)
mixed_stages=make_mixed_stages()


def make_mixed_core():
    F=fresh(FamTy,'F');Orel=fresh(Rel(Idx),'order');zero=fresh(Idx,'zero');pen=fresh(Idx,'pen');last=fresh(Idx,'last');J=fresh(Arr(X,O),'J');C=fresh(Arr(Idx,O),'coverK');i=fresh(Idx,'i');R=Total(F);M=Minima(F,J,zero)
    ass=[Fin(C),All(i,App(C,i)),irrefl(Orel),trans(Orel),tri(Orel),least(Orel,zero),LastPair(Orel,pen,last),WFcolors(F),Gzero(F,Orel,zero),Gothers(F,Orel,zero),MixedHeights(F,Orel,zero,pen,M),domain(R,J),NE(J),serial(R,J)]
    h=list(map(hyp,ass))
    stages=use(mixed_stages,[F,Orel,zero,pen,J,C],[h[7],h[0],h[1],h[4],h[9],h[11],h[10]])
    out=use(stage_core,[F,Orel,zero,pen,last,J,C],h[:10]+[stages]+h[11:])
    return lemma('serial_domain_mixed_height_impossible',out,[F,Orel,zero,pen,last,J,C],ass)
mixed_core=make_mixed_core()

# The maximal serial subset is the nonaccessible (immortal) set, using
# accessibility rather than an unmentioned dependent-choice principle.
def Immortal(R):
    x=fresh(X,'x');S=fresh(Arr(X,O),'S')
    return Lam(x,Ex(S,And(App(S,x),serial(R,S))))

def make_immortal_properties():
    R=fresh(Rel(X),'R');I=Immortal(R);x=fresh(X,'x');y=fresh(X,'y')
    def ix(hx):
        def atS(S,hS):
            def at_y(y,hy):
                iy=ei(norm(App(I,y)),S,ai(al(hy),ar(hS)))
                return ei(serial_target(R,I,x),y,ai(iy,ar(hy)))
            return unpack(mp(spec(ar(hS),x),al(hS)),at_y)
        return unpack(hx,atS)
    ser=lemma('immortal_set_is_serial',For(x,lambda x:intro(App(I,x),ix)),[R])
    def edge(rxy):
        def iy(iy):
            def atS(S,h):
                J=PredClosure(R,S)
                jx=ei(norm(App(J,x)),y,ai(use(star_cons,[R,x,y,y],[rxy,spec(star_refl,R,y)]),al(h)))
                js=use(closure_serial,[R,S],[ar(h)])
                return ei(norm(App(I,x)),J,ai(jx,js))
            return unpack(iy,atS)
        return intro(App(I,y),iy)
    back=lemma('immortal_set_is_backward_closed',gens([x,y],intro(apps(R,x,y),edge)),[R])
    ne=unpack(use(notwf_serial,[R],[hyp(Not(WF(R)))]),lambda S,h:unpack(al(h),lambda x,sx:ei(NE(I),x,ei(norm(App(I,x)),S,ai(sx,ar(h))))))
    ne=lemma('non_well_founded_union_has_immortal_point',ne,[R],[Not(WF(R))])
    return ser,back,ne
imm_serial,imm_back,imm_nonempty=make_immortal_properties()


def make_mixed_main():
    F=fresh(FamTy,'F');Orel=fresh(Rel(Idx),'order');zero=fresh(Idx,'zero');pen=fresh(Idx,'pen');last=fresh(Idx,'last');R=Total(F);I=Immortal(R);CF=CutFamily(I,F);M=Minima(CF,I,zero)
    ass=[FinType(Idx),irrefl(Orel),trans(Orel),tri(Orel),least(Orel,zero),LastPair(Orel,pen,last),WFcolors(F),Gzero(F,Orel,zero),Gothers(F,Orel,zero),MixedHeights(CF,Orel,zero,pen,M)]
    FK,OI,OT,OTT,LZ,LP,WFC,G0,Gi,Mix=map(hyp,ass)
    def nw(nw):
        BJ=spec(imm_back,R);NJ=use(imm_nonempty,[R],[nw]);SJ=spec(imm_serial,R)
        wc=use(cut_wf,[F,I],[WFC]);dc=spec(cut_domain,F,I);sc=use(cut_serial,[F,I],[SJ])
        g0=use(cut_gzero,[F,I,Orel,zero],[BJ,G0]);gi=use(cut_gothers,[F,I,Orel,zero],[BJ,Gi])
        return unpack(FK,lambda CK,hk:use(mixed_core,[CF,Orel,zero,pen,last,I,CK],[al(hk),ar(hk),OI,OT,OTT,LZ,LP,wc,g0,gi,Mix,dc,NJ,sc]))
    return lemma('arbitrary_family_mixed_height_termination',by_contra(WF(R),nw),[F,Orel,zero,pen,last],ass)
mixed_main=make_mixed_main()



def make_zero_rank_clear():
    R=fresh(Rel(X),'R');B=fresh(Rel(X),'B');J=fresh(Arr(X,O),'J');S=fresh(Arr(X,O),'S');L=fresh(Rel(Ord),'L');rho=fresh(Arr(X,Ord),'rank');a=fresh(X,'a')
    ass=[Rep(R,J,S),StrongRoute(R,B,S),tri(L),trans(L),RankDecrease(B,L,rho),RankLub(B,L,rho),MinimumRank(L,rho,S,a),ZeroRank(L,App(rho,a))]
    RS,Route,trich,tr,dec,lub,Min,Z=map(hyp,ass);alpha=App(rho,a);U=RankLayer(rho,S,alpha);x=fresh(X,'x');y=fresh(X,'y')
    nr=use(minimum_rep,[R,B,J,S,L,rho,a],[RS,Route,trich,tr,dec,lub,Min]);NU,RU=al(nr),ar(nr)
    US=For(x,lambda x:intro(App(U,x),lambda h:al(h)))
    def ux(ux):
        def edge(e):
            v=fresh(Ord,'v');smaller=eq_transport(ar(ux),Lam(v,apps(L,App(rho,y),v)),mp(spec(dec,x,y),e))
            return mp(spec(Z,App(rho,y)),smaller)
        return For(y,lambda y:intro(apps(B,x,y),edge))
    no=For(x,lambda x:intro(App(U,x),ux))
    out=ei(Clear(R,B,J,S),U,cproof(US,NU,RU,no))
    return lemma('zero_minimum_rank_clears_the_stage',out,[R,B,J,S,L,rho,a],ass)
zero_rank_clear=make_zero_rank_clear()


def InternalRanks(F,Orel,zero,pen,L,ranks):
    i=fresh(Idx,'i');B=App(F,i);rho=App(ranks,i)
    return All(i,imps([Not(Eq(i,zero)),apps(Orel,i,pen)],CAnd(Short(F,Orel,i),RankDecrease(B,L,rho),RankLub(B,L,rho))))

def OrdinalObstruction(F,Orel,zero,pen,J,L,ranks):
    i=fresh(Idx,'i');S=fresh(Arr(X,O),'S');a=fresh(X,'a');M=Minima(F,J,zero)
    return Exists([i,S,a],CAnd(Not(Eq(i,zero)),apps(Orel,i,pen),Sub(S,M),Rep(Total(F),J,S),NoFrom(Part(F,Orel,i,True),S),MinimumRank(L,App(ranks,i),S,a),LimitRank(L,apps(ranks,i,a))))

def ZeroOrSuccessorOn(F,Orel,zero,pen,J,L,ranks):
    i=fresh(Idx,'i');x=fresh(X,'x');b=fresh(Ord,'beta');a=apps(ranks,i,x);M=Minima(F,J,zero)
    return alls([i,x],imps([Not(Eq(i,zero)),apps(Orel,i,pen),App(M,x)],Or(ZeroRank(L,a),Ex(b,SuccRank(L,b,a)))))


def make_ordinal_core():
    F=fresh(FamTy,'F');Orel=fresh(Rel(Idx),'order');zero=fresh(Idx,'zero');pen=fresh(Idx,'pen');last=fresh(Idx,'last');J=fresh(Arr(X,O),'J');CK=fresh(Arr(Idx,O),'coverK');L=fresh(Rel(Ord),'rank_order');ranks=fresh(Arr(Idx,Arr(X,Ord)),'ranks');i=fresh(Idx,'i');R=Total(F);M=Minima(F,J,zero)
    common=[Fin(CK),All(i,App(CK,i)),irrefl(Orel),trans(Orel),tri(Orel),least(Orel,zero),LastPair(Orel,pen,last),WFcolors(F),Gzero(F,Orel,zero),Gothers(F,Orel,zero)]
    rest=[domain(R,J),NE(J),serial(R,J),irrefl(L),trans(L),tri(L),WF(Rev(L)),InternalRanks(F,Orel,zero,pen,L,ranks)]
    ass=common+rest;h=list(map(hyp,ass));FK,AK,OI,OT,OTT,LZ,LP,WFC,G0,Gi=h[:10];DJ,NJ,Ser,LI,LT,LTri,LWF,Ranks=h[10:]
    TW=use(family_transwf,[F,CK],[WFC,FK,AK]);ob=OrdinalObstruction(F,Orel,zero,pen,J,L,ranks)
    def no_obstruction(NoOb):
        S=fresh(Arr(X,O),'S');prem=[Not(Eq(i,zero)),apps(Orel,i,pen),Sub(S,M),NE(S),Rep(R,J,S),NoFrom(Part(F,Orel,i,True),S)]
        NZ,IP,SM,NS,RS,NP=map(hyp,prem);B=App(F,i);rho=App(ranks,i)
        rd=apply(spec(Ranks,i),NZ,IP);Shorti,Dec,Lub=[proj(rd,k,3) for k in range(3)]
        route=use(strong_stage_route,[F,Orel,zero,i,S],[OTT,NP,Shorti,NZ])
        x=fresh(X,'x');y=fresh(X,'y');BR=gens([x,y],intro(apps(B,x,y),lambda e:use(color_total,[F,i,x,y],[e])))
        minimum=use(rank_minimum,[L,rho,S],[LWF,NS])
        def ata(a,mn):
            noSucc=use(minimum_not_successor,[R,B,J,S,L,rho,a],[TW,BR,DJ,RS,route,LI,LTri,LT,Dec,Lub,mn])
            alpha=App(rho,a)
            def zero(z):return use(zero_rank_clear,[R,B,J,S,L,rho,a],[RS,route,LTri,LT,Dec,Lub,mn,z])
            def nonzero(nz):
                body=cproof(NZ,IP,SM,RS,NP,mn,ai(nz,noSucc))
                # Nested existential witness i,S,a, with capture-safe substitution.
                f=norm(ob);fi=subst(f[2],f[1],i);fs=subst(fi[2],fi[1],S)
                wit=ei(f,i,ei(fi,S,ei(fs,a,body)))
                return absurd(mp(NoOb,wit),Clear(R,B,J,S))
            return cases(em(ZeroRank(L,alpha)),zero,nonzero)
        stage=unpack(minimum,ata)
        St=gens([i,S],iis(prem,stage))
        return use(stage_core,[F,Orel,zero,pen,last,J,CK],h[:10]+[St]+h[10:13])
    out=by_contra(ob,no_obstruction)
    return lemma('serial_family_has_a_nonzero_limit_rank_layer',out,[F,Orel,zero,pen,last,J,CK,L,ranks],ass)
ordinal_core=make_ordinal_core()


def make_ordinal_main():
    F=fresh(FamTy,'F');Orel=fresh(Rel(Idx),'order');zero=fresh(Idx,'zero');pen=fresh(Idx,'pen');last=fresh(Idx,'last');L=fresh(Rel(Ord),'rank_order');ranks=fresh(Arr(Idx,Arr(X,Ord)),'ranks')
    R=Total(F);I=Immortal(R);CF=CutFamily(I,F)
    ass=[FinType(Idx),irrefl(Orel),trans(Orel),tri(Orel),least(Orel,zero),LastPair(Orel,pen,last),WFcolors(F),Gzero(F,Orel,zero),Gothers(F,Orel,zero),irrefl(L),trans(L),tri(L),WF(Rev(L)),InternalRanks(CF,Orel,zero,pen,L,ranks),Not(WF(R))]
    FK,OI,OT,OTT,LZ,LP,WFC,G0,Gi,LI,LT,LTri,LWF,Ranks,NW=map(hyp,ass)
    BJ=spec(imm_back,R);NJ=use(imm_nonempty,[R],[NW]);SJ=spec(imm_serial,R)
    wc=use(cut_wf,[F,I],[WFC]);dc=spec(cut_domain,F,I);sc=use(cut_serial,[F,I],[SJ])
    g0=use(cut_gzero,[F,I,Orel,zero],[BJ,G0]);gi=use(cut_gothers,[F,I,Orel,zero],[BJ,Gi])
    out=unpack(FK,lambda CK,hk:use(ordinal_core,[CF,Orel,zero,pen,last,I,CK,L,ranks],[al(hk),ar(hk),OI,OT,OTT,LZ,LP,wc,g0,gi,dc,NJ,sc,LI,LT,LTri,LWF,Ranks]))
    return lemma('arbitrary_family_limit_rank_obstruction',out,[F,Orel,zero,pen,last,L,ranks],ass)
ordinal_main=make_ordinal_main()


def make_successor_rank_termination():
    F=fresh(FamTy,'F');Orel=fresh(Rel(Idx),'order');zero=fresh(Idx,'zero');pen=fresh(Idx,'pen');last=fresh(Idx,'last');L=fresh(Rel(Ord),'rank_order');ranks=fresh(Arr(Idx,Arr(X,Ord)),'ranks')
    R=Total(F);I=Immortal(R);CF=CutFamily(I,F);M=Minima(CF,I,zero)
    ass=[FinType(Idx),irrefl(Orel),trans(Orel),tri(Orel),least(Orel,zero),LastPair(Orel,pen,last),WFcolors(F),Gzero(F,Orel,zero),Gothers(F,Orel,zero),irrefl(L),trans(L),tri(L),WF(Rev(L)),InternalRanks(CF,Orel,zero,pen,L,ranks),ZeroOrSuccessorOn(CF,Orel,zero,pen,I,L,ranks)]
    hs=list(map(hyp,ass));ZOS=hs[-1]
    def nw(nw):
        ob=use(ordinal_main,[F,Orel,zero,pen,last,L,ranks],hs[:-1]+[nw])
        def ati(i,hi):
            def atS(S,hS):
                def ata(a,h):
                    NZ,IP,SM,RS,NP,Mn,Lim=[proj(h,k,7) for k in range(7)]
                    ma=mp(spec(SM,a),al(Mn));casesa=apply(spec(ZOS,i,a),NZ,IP,ma)
                    return cases(casesa,lambda z:mp(al(Lim),z),lambda succ:mp(ar(Lim),succ))
                return unpack(hS,ata)
            return unpack(hi,atS)
        return unpack(ob,ati)
    return lemma('zero_or_successor_internal_ranks_imply_termination',by_contra(WF(R),nw),[F,Orel,zero,pen,last,L,ranks],ass)
successor_rank_termination=make_successor_rank_termination()

# Name the graph-theoretic conclusion explicitly, as distinct from finiteness.
def Acyclic(R):
    x=fresh(type_of(R)[1],'x');return All(x,Not(Plus(R,x,x)))

def make_finite_acyclic_conclusion():
    F=fresh(FamTy,'F');Orel=fresh(Rel(Idx),'order');zero=fresh(Idx,'zero');i=fresh(Idx,'i')
    AC=All(i,Acyclic(App(F,i)))
    ass=[FinType(X),FinType(Idx),irrefl(Orel),trans(Orel),tri(Orel),least(Orel,zero),AC,Gzero(F,Orel,zero),Gothers(F,Orel,zero)]
    hs=list(map(hyp,ass));wf=use(main_acyclic,[F,Orel,zero],hs)
    out=use(wf_acyclic,[Total(F)],[wf])
    return lemma('arbitrary_finite_acyclic_family_has_acyclic_union',out,[F,Orel,zero],ass)
finite_acyclic_conclusion=make_finite_acyclic_conclusion()



def MixedOrdinal(F,Orel,zero,pen,J,L,ranks):
    i=fresh(Idx,'i');x=fresh(X,'x');beta=fresh(Ord,'beta');B=App(F,i);rho=App(ranks,i);M=Minima(F,J,zero);alpha=App(rho,x)
    zos=All(x,Imp(App(M,x),Or(ZeroRank(L,alpha),Ex(beta,SuccRank(L,beta,alpha)))))
    rk=CAnd(Short(F,Orel,i),RankDecrease(B,L,rho),RankLub(B,L,rho),zos)
    return All(i,imps([Not(Eq(i,zero)),apps(Orel,i,pen)],Or(Bounded(B,M),rk)))

def make_mixed_ordinal_stages():
    F=fresh(FamTy,'F');Orel=fresh(Rel(Idx),'order');zero=fresh(Idx,'zero');pen=fresh(Idx,'pen');J=fresh(Arr(X,O),'J');CK=fresh(Arr(Idx,O),'coverK');L=fresh(Rel(Ord),'rank_order');ranks=fresh(Arr(Idx,Arr(X,Ord)),'ranks');i=fresh(Idx,'i');R=Total(F);M=Minima(F,J,zero)
    ass=[WFcolors(F),Fin(CK),All(i,App(CK,i)),tri(Orel),Gothers(F,Orel,zero),domain(R,J),irrefl(L),trans(L),tri(L),WF(Rev(L)),MixedOrdinal(F,Orel,zero,pen,J,L,ranks)]
    WFC,FCc,AC,TT,GI,DJ,LI,LT,LTri,LWF,Mix=map(hyp,ass)
    TW=use(family_transwf,[F,CK],[WFC,FCc,AC]);S=fresh(Arr(X,O),'S')
    prem=[Not(Eq(i,zero)),apps(Orel,i,pen),Sub(S,M),NE(S),Rep(R,J,S),NoFrom(Part(F,Orel,i,True),S)]
    NZ,IP,SM,NS,RS,NP=map(hyp,prem);B=App(F,i);rho=App(ranks,i)
    x=fresh(X,'x');y=fresh(X,'y')
    SJ=For(x,lambda x:intro(App(S,x),lambda sx:al(mp(spec(SM,x),sx))))
    BR=gens([x,y],intro(apps(B,x,y),lambda e:use(color_total,[F,i,x,y],[e])))
    def uniform(b):
        def atH(H,h):
            bound=use(subset_trans,[S,M,Next(B,H)],[SM,ar(h)])
            Hb=ei(Bounded(B,S),H,ai(al(h),bound))
            route=use(full_stage_route,[F,Orel,zero,i,S],[TT,NP,GI,NZ])
            return use(uniform_clear,[R,B,J,S],[TW,BR,DJ,SJ,NS,RS,route,Hb])
        return unpack(b,atH)
    def ordinal(h):
        Shorti,Dec,Lub,ZOS=[proj(h,k,4) for k in range(4)]
        route=use(strong_stage_route,[F,Orel,zero,i,S],[TT,NP,Shorti,NZ])
        def ata(a,mn):
            noSucc=use(minimum_not_successor,[R,B,J,S,L,rho,a],[TW,BR,DJ,RS,route,LI,LTri,LT,Dec,Lub,mn])
            ma=mp(spec(SM,a),al(mn));za=mp(spec(ZOS,a),ma)
            return cases(za,lambda z:use(zero_rank_clear,[R,B,J,S,L,rho,a],[RS,route,LTri,LT,Dec,Lub,mn,z]),lambda s:absurd(mp(noSucc,s),Clear(R,B,J,S)))
        return unpack(use(rank_minimum,[L,rho,S],[LWF,NS]),ata)
    out=cases(apply(spec(Mix,i),NZ,IP),uniform,ordinal)
    return lemma('mixed_height_and_ordinal_stages_are_eliminable',gens([i,S],iis(prem,out)),[F,Orel,zero,pen,J,CK,L,ranks],ass)
mixed_ordinal_stages=make_mixed_ordinal_stages()


def make_mixed_ordinal_main():
    F=fresh(FamTy,'F');Orel=fresh(Rel(Idx),'order');zero=fresh(Idx,'zero');pen=fresh(Idx,'pen');last=fresh(Idx,'last');L=fresh(Rel(Ord),'rank_order');ranks=fresh(Arr(Idx,Arr(X,Ord)),'ranks');R=Total(F);I=Immortal(R);CF=CutFamily(I,F)
    ass=[FinType(Idx),irrefl(Orel),trans(Orel),tri(Orel),least(Orel,zero),LastPair(Orel,pen,last),WFcolors(F),Gzero(F,Orel,zero),Gothers(F,Orel,zero),irrefl(L),trans(L),tri(L),WF(Rev(L)),MixedOrdinal(CF,Orel,zero,pen,I,L,ranks)]
    FK,OI,OT,OTT,LZ,LP,WFC,G0,Gi,LI,LT,LTri,LWF,Mix=map(hyp,ass)
    def nw(nw):
        BJ=spec(imm_back,R);NJ=use(imm_nonempty,[R],[nw]);SJ=spec(imm_serial,R)
        wc=use(cut_wf,[F,I],[WFC]);dc=spec(cut_domain,F,I);sc=use(cut_serial,[F,I],[SJ])
        g0=use(cut_gzero,[F,I,Orel,zero],[BJ,G0]);gi=use(cut_gothers,[F,I,Orel,zero],[BJ,Gi])
        def atCK(CK,hk):
            stages=use(mixed_ordinal_stages,[CF,Orel,zero,pen,I,CK,L,ranks],[wc,al(hk),ar(hk),OTT,gi,dc,LI,LT,LTri,LWF,Mix])
            return use(stage_core,[CF,Orel,zero,pen,last,I,CK],[al(hk),ar(hk),OI,OT,OTT,LZ,LP,wc,g0,gi,stages,dc,NJ,sc])
        return unpack(FK,atCK)
    return lemma('arbitrary_family_mixed_height_and_ordinal_termination',by_contra(WF(R),nw),[F,Orel,zero,pen,last,L,ranks],ass)
mixed_ordinal_main=make_mixed_ordinal_main()


# Bridge the maximal serial subset used in the certificate to the manuscript's
# pointwise accessibility definition, without dependent choice.
def Inductive(R,H):
    x=fresh(X,'x');y=fresh(X,'y')
    return All(x,Imp(All(y,Imp(apps(R,x,y),App(H,y))),App(H,x)))
def Accessible(R,x):
    H=fresh(Arr(X,O),'H');return All(H,Imp(Inductive(R,H),App(H,x)))

def make_immortal_accessibility():
    R=fresh(Rel(X),'R');x=fresh(X,'x');I=Immortal(R)
    def imm_to_notacc(ix):
        def atS(S,hS):
            sx,ss=al(hS),ar(hS);v=fresh(X,'v');w=fresh(X,'w');H=Lam(v,Not(App(S,v)))
            ih=All(w,Imp(apps(R,v,w),Not(App(S,w))))
            def induct(h):
                return intro(App(S,v),lambda sv:unpack(mp(spec(ss,v),sv),lambda w,hw:mp(mp(spec(h,w),ar(hw)),al(hw))))
            ind=For(v,lambda v:intro(ih,induct))
            return intro(Accessible(R,x),lambda acc:mp(mp(spec(acc,H),ind),sx))
        return unpack(ix,atS)
    forward=intro(App(I,x),imm_to_notacc)
    def notacc_to_imm(na):
        H=fresh(Arr(X,O),'H');goal=Ex(H,And(Inductive(R,H),Not(App(H,x))))
        def nog(nh):
            def inductH(ind):
                return by_contra(App(H,x),lambda notx:mp(nh,ei(goal,H,ai(ind,notx))))
            return mp(na,For(H,lambda H:intro(Inductive(R,H),inductH)))
        got=by_contra(goal,nog)
        def atH(H,hH):
            ind,nx=al(hH),ar(hH);v=fresh(X,'v');w=fresh(X,'w');S=Lam(v,Not(App(H,v)))
            def serialv(nv):
                g=Ex(w,And(App(S,w),apps(R,v,w)))
                def nosucc(ns):
                    allgood=For(w,lambda w:intro(apps(R,v,w),lambda e:by_contra(App(H,w),lambda nw:mp(ns,ei(g,w,ai(nw,e))))))
                    return mp(nv,mp(spec(ind,v),allgood))
                return by_contra(g,nosucc)
            ss=For(v,lambda v:intro(App(S,v),serialv))
            return ei(norm(App(I,x)),S,ai(nx,ss))
        return unpack(got,atH)
    reverse=intro(Not(Accessible(R,x)),notacc_to_imm)
    return lemma('immortal_iff_nonaccessible',ai(forward,reverse),[R,x])
immortal_accessibility=make_immortal_accessibility()

save_certificate(K,THEOREMS,'proof.json')
print('EXTENDED CERTIFICATE',len(K.records),len(THEOREMS))
