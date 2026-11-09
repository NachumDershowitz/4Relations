"""Construct a branching-extension certificate using ordinary checked ND rules.
The checker has no branching, finiteness, or termination rule.
"""
from base_build import *
BASE_THEOREM_NAMES = frozenset(THEOREMS)

def CAnd(*xs):
    out=xs[-1]
    for x in reversed(xs[:-1]):out=And(x,out)
    return out

def cproof(*ps):
    out=ps[-1]
    for p in reversed(ps[:-1]):out=ai(p,out)
    return out

def proj(p,i,n):
    for _ in range(i):p=ar(p)
    return p if i==n-1 else al(p)

def Exists(vs,b):
    for v in reversed(vs):b=Ex(v,b)
    return b

def FC(S):
    c=fresh(type_of(S),'cover')
    return Ex(c,And(Fin(c),Sub(S,c)))

def Sum(U,Vv):
    x=fresh(type_of(U)[1],'x');return Lam(x,Or(App(U,x),App(Vv,x)))

def Image(B,S):
    z=fresh(type_of(S)[1],'z');x=fresh(type_of(S)[1],'x')
    return Lam(z,Ex(x,And(App(S,x),apps(B,x,z))))

def Desc(B,a):
    z=fresh(type_of(a),'z');return Lam(z,Plus(B,a,z))

def Reach(B,a):
    z=fresh(type_of(a),'z');return Lam(z,Star(B,a,z))

def FB(B):
    x=fresh(type_of(B)[1],'x');y=fresh(type_of(x),'y')
    return All(x,FC(Lam(y,apps(B,x,y))))

def NoFrom(B,S):
    x=fresh(type_of(S)[1],'x');return All(x,Imp(App(S,x),No(B,x)))

def SubRel(B,R):
    x=fresh(type_of(B)[1],'x');y=fresh(type_of(x),'y')
    return alls([x,y],Imp(apps(B,x,y),apps(R,x,y)))

# A finite cover of the union of two finite generated sets; no extensionality.
def make_finite_combine():
    U=fresh(Arr(X,O),'U');Vv=fresh(Arr(X,O),'V');c=fresh(Arr(X,O),'C')
    def outcome(U):return Ex(c,CAnd(Fin(c),Sub(U,c),Sub(Vv,c)))
    x=fresh(X,'x')
    emp=For(x,lambda x:intro(App(Empty(X),x),lambda h:absurd(h,App(Vv,x))))
    base=ei(outcome(Empty(X)),Vv,cproof(hyp(Fin(Vv)),emp,spec(subset_refl,Vv)))
    a=fresh(X,'a');L=fresh(Arr(X,O),'L')
    def st(ih):
        def get(C,h):
            f,uc,vc=[proj(h,i,3) for i in range(3)]
            W=Ins(a,C);w=fresh(X,'w');x=fresh(X,'x')
            subu=For(x,lambda x:intro(App(Ins(a,L),x),lambda q:cases(q,lambda e:ol(e,App(C,x)),lambda lx:ore(mp(spec(uc,x),lx),Eq(x,a)))))
            subv=For(x,lambda x:intro(App(Vv,x),lambda vx:ore(mp(spec(vc,x),vx),Eq(x,a))))
            return ei(outcome(Ins(a,L)),W,cproof(use(finite_insert,[C,a],[f]),subu,subv))
        return unpack(ih,get)
    step=gens([a,L],intro(outcome(L),st))
    p=fresh(Arr(X,O),'U')
    out=apply(spec(hyp(Fin(U)),Lam(p,outcome(p))),base,step)
    return lemma('finite_union_cover',out,[U,Vv],[Fin(U),Fin(Vv)])
finite_combine=make_finite_combine()

# Finitely many pointwise finite families admit one finite covering set.
def make_finite_aggregate():
    L=fresh(Arr(X,O),'L');T=fresh(Rel(X),'T')
    y=fresh(X,'y');z=fresh(X,'z');C=fresh(Arr(X,O),'C')
    def rows(L):
        y=fresh(X,'y');z=fresh(X,'z')
        return All(y,Imp(App(L,y),FC(Lam(z,apps(T,y,z)))))
    def out(L):
        y=fresh(X,'y');z=fresh(X,'z')
        return Ex(C,And(Fin(C),alls([y,z],imps([App(L,y),apps(T,y,z)],App(C,z)))))
    basecover=gens([y,z],intro(App(Empty(X),y),lambda h:intro(apps(T,y,z),lambda _:absurd(h,App(Empty(X),z)))))
    base=ii(rows(Empty(X)),ei(out(Empty(X)),Empty(X),ai(finite_empty,basecover)))
    a=fresh(X,'a');U=fresh(Arr(X,O),'U')
    def stepfn(ih):
        def withrows(hr):
            y=fresh(X,'y')
            tailrows=For(y,lambda y:intro(App(U,y),lambda uy:mp(spec(hr,y),ore(uy,Eq(y,a)))))
            old=mp(ih,tailrows);first=mp(spec(hr,a),ol(refl(a),App(U,a)))
            def cu(Cu,hu):
                def ca(Ca,ha):
                    combined=use(finite_combine,[Cu,Ca],[al(hu),al(ha)])
                    def cc(Cc,hc):
                        f,scu,sca=[proj(hc,i,3) for i in range(3)]
                        y=fresh(X,'y');z=fresh(X,'z');w=fresh(X,'w')
                        def cy(iy):
                            def tz(edge):
                                def equ(eq):
                                    az=eq_transport(eq,Lam(w,apps(T,w,z)),edge)
                                    return mp(spec(sca,z),mp(spec(ar(ha),z),az))
                                return cases(iy,equ,lambda uy:mp(spec(scu,z),apply(spec(ar(hu),y,z),uy,edge)))
                            return intro(apps(T,y,z),tz)
                        cover=gens([y,z],intro(App(Ins(a,U),y),cy))
                        return ei(out(Ins(a,U)),Cc,ai(f,cover))
                    return unpack(combined,cc)
                return unpack(first,ca)
            return unpack(old,cu)
        return intro(rows(Ins(a,U)),withrows)
    step=gens([a,U],intro(Imp(rows(U),out(U)),stepfn))
    u=fresh(Arr(X,O),'u');res=apply(spec(hyp(Fin(L)),Lam(u,Imp(rows(u),out(u)))),base,step,hyp(rows(L)))
    return lemma('finite_pointwise_cover_aggregation',res,[L,T],[Fin(L),rows(L)])
finite_aggregate=make_finite_aggregate()

# Well-founded finitely branching relations have finitely covered reachability.
def make_finite_descendants():
    B=fresh(Rel(X),'B');x=fresh(X,'x');y=fresh(X,'y');z=fresh(X,'z');C=fresh(Arr(X,O),'C')
    def hf(x):return FC(Reach(B,x))
    ih=All(y,Imp(apps(B,x,y),hf(y)))
    def stepfn(hi):
        targets=spec(hyp(FB(B)),x)
        def withL(L,hl):
            # Aggregate only actual successors; the cover may contain extra points.
            y=fresh(X,'y');z=fresh(X,'z')
            T=Lam(y,Lam(z,And(apps(B,x,y),Star(B,y,z))))
            def row(ly):
                def yes(edge):
                    def got(Cy,hcy):
                        cz=For(z,lambda z:intro(apps(T,y,z),lambda h:mp(spec(ar(hcy),z),ar(h))))
                        return ei(FC(Lam(z,apps(T,y,z))),Cy,ai(al(hcy),cz))
                    return unpack(mp(spec(hi,y),edge),got)
                def no(ne):
                    cz=For(z,lambda z:intro(apps(T,y,z),lambda h:mp(ne,al(h))))
                    return ei(FC(Lam(z,apps(T,y,z))),Empty(X),ai(finite_empty,cz))
                return cases(em(apps(B,x,y)),yes,no)
            rows=For(y,lambda y:intro(App(L,y),row))
            agg=use(finite_aggregate,[L,T],[al(hl),rows])
            def withC(Cc,hc):
                Vv=Ins(x,Cc);z=fresh(X,'z')
                def atz(path):
                    def eqcase(eq):
                        return ol(use(eq_sym,[x,z],[eq]),App(Cc,z))
                    def pos(pp):
                        def via(u,hu):
                            lu=mp(spec(ar(hl),u),al(hu))
                            cz=apply(spec(ar(hc),u,z),lu,ai(al(hu),ar(hu)))
                            return ore(cz,Eq(z,x))
                        return unpack(pp,via)
                    return cases(use(star_split,[B,x,z],[path]),eqcase,pos)
                cov=For(z,lambda z:intro(Star(B,x,z),atz))
                return ei(hf(x),Vv,ai(use(finite_insert,[Cc,x],[al(hc)]),cov))
            return unpack(agg,withC)
        return unpack(targets,withL)
    step=For(x,lambda x:intro(ih,stepfn))
    p=fresh(X,'x');res=mp(spec(hyp(WF(B)),Lam(p,hf(p))),step)
    return lemma('well_founded_finitely_branching_finite_reachability',res,[B],[WF(B),FB(B)])
finite_reach=make_finite_descendants()

# Appending a reflexive-transitive path to a positive path remains positive.
def make_plus_append():
    B=fresh(Rel(X),'B');x=fresh(X,'x');y=fresh(X,'y');z=fresh(X,'z')
    p=unpack(hyp(Plus(B,x,y)),lambda u,h:ei(Plus(B,x,z),u,ai(al(h),use(star_trans,[B,u,y,z],[ar(h),hyp(Star(B,y,z))]))))
    return lemma('positive_path_followed_by_path',p,[B,x,y,z],[Plus(B,x,y),Star(B,y,z)])
plus_append=make_plus_append()


# Finite target covers suffice to eliminate a relation, even on an infinite carrier.
def LocalRoute(R,B,S):
    x=fresh(X,'x');y=fresh(X,'y');z=fresh(X,'z')
    return alls([x,y,z],imps([App(S,x),App(S,y),apps(R,x,y),apps(B,y,z)],Or(Plus(B,x,z),apps(R,x,z))))

def Clear(R,B,J,S):
    U=fresh(Arr(X,O),'U')
    return Ex(U,CAnd(Sub(U,S),NE(U),Rep(R,J,U),NoFrom(B,U)))

def image_member(B,S,z,x,sx,edge):
    return ei(norm(App(Image(B,S),z)),x,ai(sx,edge))

def make_clear_finite_image():
    R=fresh(Rel(X),'R');B=fresh(Rel(X),'B');J=fresh(Arr(X,O),'J');S=fresh(Arr(X,O),'S');C=fresh(Arr(X,O),'C')
    ass=[irrefl(R),WF(B),SubRel(B,R),domain(R,J),Sub(S,J),NE(S),Rep(R,J,S),LocalRoute(R,B,S),Fin(C),Sub(Image(B,S),C)]
    IR,WB,BR,Dom,SJ,NS,RS,Route,FinC,ImgC=map(hyp,ass)
    Vv=fresh(Arr(X,O),'V');U=fresh(Arr(X,O),'U')
    def good(Vv):return Ex(U,CAnd(Sub(U,S),NE(U),Rep(R,J,U),Sub(Image(B,U),Vv)))
    G=Lam(Vv,good(Vv))
    candG=ei(good(C),S,cproof(spec(subset_refl,S),NS,RS,ImgC))
    candidate=ei(candidate_ex(G,C),C,ai(spec(subset_refl,C),candG))
    mini=mp(spec(mp(spec(finite_minimal_subset,C),FinC),G),candidate)
    def withV(Vv,hv):
        VC=al(hv);gv=al(ar(hv));minimum=ar(ar(hv))
        def withU(U,hu):
            US,NU,RU,ImgV=[proj(hu,i,4) for i in range(4)]
            Im=Image(B,U)
            def image_empty(noimg):
                x=fresh(X,'x');z=fresh(X,'z')
                no=For(x,lambda x:intro(App(U,x),lambda ux:For(z,lambda z:intro(apps(B,x,z),lambda e:mp(noimg,ei(NE(Im),z,image_member(B,U,z,x,ux,e)))))))
                return ei(Clear(R,B,J,S),U,cproof(US,NU,RU,no))
            def image_nonempty(neimg):
                x=fresh(X,'x');y=fresh(X,'y');z=fresh(X,'z')
                TP=Lam(x,Lam(y,Plus(B,x,y)))
                tr=gens([x,y,z],iis([Plus(B,x,y),Plus(B,y,z)],use(plus_trans,[B,x,y,z],[hyp(Plus(B,x,y)),hyp(Plus(B,y,z))])))
                ir=mp(spec(wf_acyclic,B),WB)
                imc=use(subset_trans,[Im,Vv,C],[ImgV,VC])
                chosen=apply(spec(apply(spec(finite_source,TP,C),ir,tr,FinC),Im),imc,neimg)
                def atz(z,hz):
                    imz=al(hz);zmin=ar(hz)
                    def nlong(x,u,ux,bxu,upz):
                        return mp(mp(spec(zmin,u),image_member(B,U,u,x,ux,bxu)),upz)
                    jz=unpack(imz,lambda x,h:ar(mp(spec(Dom,x,z),mp(spec(BR,x,z),ar(h)))))
                    repz=mp(spec(RU,z),jz)
                    def att(t,ht):
                        ut=al(ht);rt=ar(ht)
                        def not_bt(e):return mp(spec(IR,t),apply(spec(rt,t),ut,mp(spec(BR,t,z),e)))
                        nbt=intro(apps(B,t,z),not_bt)
                        x=fresh(X,'x');y=fresh(X,'y')
                        def transferx(ux):
                            def transfery(uy):
                                def transferb(byz):
                                    def transferr(rxy):
                                        casesxz=apply(spec(Route,x,y,z),mp(spec(US,x),ux),mp(spec(US,y),uy),rxy,byz)
                                        def pcase(pxz):
                                            def atw(w,hw):
                                                def eqcase(eq):
                                                    v=fresh(X,'v');bxz=eq_transport(eq,Lam(v,apps(B,x,v)),al(hw))
                                                    return mp(spec(BR,x,z),bxz)
                                                return cases(use(star_split,[B,w,z],[ar(hw)]),eqcase,lambda wpz:absurd(nlong(x,w,ux,al(hw),wpz),apps(R,x,z)))
                                            return unpack(pxz,atw)
                                        rxz=cases(casesxz,pcase,lambda rxz:rxz)
                                        return apply(spec(rt,x),ux,rxz)
                                    return intro(apps(R,x,y),transferr)
                                return intro(apps(B,y,z),transferb)
                            return intro(App(U,y),transfery)
                        transfer=gens([x,y],intro(App(U,x),transferx))
                        x=fresh(X,'x');Up=Lam(x,And(App(U,x),Not(apps(B,x,z))))
                        UpU=For(x,lambda x:intro(App(Up,x),lambda h:al(h)))
                        UpS=use(subset_trans,[Up,U,S],[UpU,US])
                        NUp=ei(NE(Up),t,ai(ut,nbt))
                        RUp=use(fold_rep,[R,B,J,U,z,t],[RU,ut,nbt,transfer])
                        Vp=Del(Vv,z);w=fresh(X,'w')
                        def inimage(imw):
                            def fromx(x,hx):
                                v=fresh(X,'v');upx=al(hx);edge=ar(hx)
                                vw=mp(spec(ImgV,w),image_member(B,U,w,x,al(upx),edge))
                                ne=intro(Eq(w,z),lambda eq:mp(ar(upx),eq_transport(eq,Lam(v,apps(B,x,v)),edge)))
                                return ai(vw,ne)
                            return unpack(imw,fromx)
                        UpVp=For(w,lambda w:intro(App(Image(B,Up),w),inimage))
                        goodVp=ei(good(Vp),Up,cproof(UpS,NUp,RUp,UpVp))
                        VpV=For(w,lambda w:intro(App(Vp,w),lambda h:al(h)))
                        VVprime=apply(spec(minimum,Vp),VpV,goodVp)
                        vz=mp(spec(ImgV,z),imz)
                        bad=mp(ar(mp(spec(VVprime,z),vz)),refl(z))
                        return absurd(bad,Clear(R,B,J,S))
                    return unpack(repz,att)
                return unpack(chosen,atz)
            return cases(em(NE(Im)),image_nonempty,image_empty)
        return unpack(gv,withU)
    return lemma('finite_image_representative_elimination',unpack(mini,withV),[R,B,J,S,C],ass)
clear_finite=make_clear_finite_image()

# Strong rerouting propagates every nonempty B path across a union edge.
def StrongRoute(R,B,S):
    x=fresh(X,'x');y=fresh(X,'y');z=fresh(X,'z')
    return alls([x,y,z],imps([App(S,x),App(S,y),apps(R,x,y),apps(B,y,z)],Plus(B,x,z)))

def make_propagate():
    R=fresh(Rel(X),'R');B=fresh(Rel(X),'B');S=fresh(Arr(X,O),'S')
    x=fresh(X,'x');y=fresh(X,'y');z=fresh(X,'z')
    ass=[StrongRoute(R,B,S),App(S,x),App(S,y),apps(R,x,y),Plus(B,y,z)]
    route,sx,sy,rxy,pyz=map(hyp,ass)
    p=unpack(pyz,lambda u,h:use(plus_append,[B,x,u,z],[apply(spec(route,x,y,u),sx,sy,rxy,al(h)),ar(h)]))
    return lemma('short_rerouting_propagates_positive_paths',p,[R,B,S,x,y,z],ass)
propagate_plus=make_propagate()

# One point with finite B reachability provides a finite-image representative subset.
def make_branching_stage():
    R=fresh(Rel(X),'R');B=fresh(Rel(X),'B');J=fresh(Arr(X,O),'J');S=fresh(Arr(X,O),'S');a=fresh(X,'a');C=fresh(Arr(X,O),'C')
    ass=[irrefl(R),WF(B),SubRel(B,R),domain(R,J),Sub(S,J),Rep(R,J,S),StrongRoute(R,B,S),App(S,a),Fin(C),Sub(Reach(B,a),C)]
    IR,WB,BR,Dom,SJ,RepS,Route,Sa,FCc,ReachC=map(hyp,ass)
    x=fresh(X,'x');z=fresh(X,'z')
    def included(x):
        z=fresh(X,'z');return All(z,Imp(Plus(B,x,z),Plus(B,a,z)))
    L=Lam(x,And(App(S,x),included(x)))
    ila=For(z,lambda z:intro(Plus(B,a,z),lambda h:h))
    La=ai(Sa,ila);NL=ei(NE(L),a,La)
    LS=For(x,lambda x:intro(App(L,x),lambda h:al(h)))
    LJ=use(subset_trans,[L,S,J],[LS,SJ])
    def descend(x,t,lx,st,rxt):
        z=fresh(X,'z')
        inc=For(z,lambda z:intro(Plus(B,t,z),lambda ptz:mp(spec(ar(lx),z),use(propagate_plus,[R,B,S,x,t,z],[Route,al(lx),st,rxt,ptz]))))
        return ai(st,inc)
    v=fresh(X,'v')
    def repv(jv):
        old=mp(spec(RepS,v),jv)
        def witht(t,ht):
            st=al(ht);rep=ar(ht);x=fresh(X,'x')
            incoming=Ex(x,And(App(L,x),apps(R,x,v)))
            def yes(got):
                def withx(x,hx):
                    lt=descend(x,t,al(hx),st,apply(spec(rep,x),al(al(hx)),ar(hx)))
                    xx=fresh(X,'x')
                    newr=For(xx,lambda xx:intro(App(L,xx),lambda lx:intro(apps(R,xx,v),lambda e:apply(spec(rep,xx),al(lx),e))))
                    return ei(rep_target(R,J,L,v),t,ai(lt,newr))
                return unpack(got,withx)
            def no(ngot):
                xx=fresh(X,'x')
                newr=For(xx,lambda xx:intro(App(L,xx),lambda lx:intro(apps(R,xx,v),lambda e:absurd(mp(ngot,ei(incoming,xx,ai(lx,e))),apps(R,xx,a)))))
                return ei(rep_target(R,J,L,v),a,ai(La,newr))
            return cases(em(incoming),yes,no)
        return unpack(old,witht)
    RL=For(v,lambda v:intro(App(J,v),repv))
    z=fresh(X,'z')
    def imcz(imz):
        def withx(x,h):
            p=mp(spec(ar(al(h)),z),use(plus_one,[B,x,z],[ar(h)]))
            return mp(spec(ReachC,z),use(plus_star,[B,a,z],[p]))
        return unpack(imz,withx)
    ImC=For(z,lambda z:intro(App(Image(B,L),z),imcz))
    x=fresh(X,'x');y=fresh(X,'y');z=fresh(X,'z')
    routeL=gens([x,y,z],intro(App(L,x),lambda lx:intro(App(L,y),lambda ly:intro(apps(R,x,y),lambda e:intro(apps(B,y,z),lambda b:ol(apply(spec(Route,x,y,z),al(lx),al(ly),e,b),apps(R,x,z)))))))
    cleared=use(clear_finite,[R,B,J,L,C],[IR,WB,BR,Dom,LJ,NL,RL,routeL,FCc,ImC])
    def finish(U,hu):
        UL,NU,RU,BU=[proj(hu,i,4) for i in range(4)]
        US=use(subset_trans,[U,L,S],[UL,LS])
        return ei(Clear(R,B,J,S),U,cproof(US,NU,RU,BU))
    return lemma('finite_reachability_clears_shortened_stage',unpack(cleared,finish),[R,B,J,S,a,C],ass)
clear_reachable=make_branching_stage()

# The finite-branching stage theorem follows with no global height bound.
def make_fb_clear():
    R=fresh(Rel(X),'R');B=fresh(Rel(X),'B');J=fresh(Arr(X,O),'J');S=fresh(Arr(X,O),'S')
    ass=[irrefl(R),WF(B),SubRel(B,R),domain(R,J),Sub(S,J),NE(S),Rep(R,J,S),StrongRoute(R,B,S),FB(B)]
    IR,WB,BR,Dom,SJ,NS,RepS,Route,FBb=map(hyp,ass)
    def witha(a,sa):
        got=spec(use(finite_reach,[B],[WB,FBb]),a)
        return unpack(got,lambda C,h:use(clear_reachable,[R,B,J,S,a,C],[IR,WB,BR,Dom,SJ,RepS,Route,sa,al(h),ar(h)]))
    return lemma('finitely_branching_representative_elimination',unpack(NS,witha),[R,B,J,S],ass)
clear_branching=make_fb_clear()


# Binary jumping closes the final two relations without branching assumptions.
def Cup(P,Q):
    x=fresh(type_of(P)[1],'x');y=fresh(type_of(x),'y')
    return Lam(x,Lam(y,Or(apps(P,x,y),apps(Q,x,y))))

def BinaryRoute(P,Q):
    x=fresh(X,'x');y=fresh(X,'y');z=fresh(X,'z')
    return alls([x,y,z],imps([apps(Q,x,y),apps(P,y,z)],Or(Plus(P,x,z),apps(Q,x,z))))

def make_serial_binary():
    P0=fresh(Rel(X),'P');Q=fresh(Rel(X),'Q');J=fresh(Arr(X,O),'J');E=Cup(P0,Q)
    ass=[WF(P0),WF(Q),domain(E,J),NE(J),serial(E,J),BinaryRoute(P0,Q)]
    WP,WQ,Dom,NJ,SJ,Route=map(hyp,ass)
    x=fresh(X,'x');M=Lam(x,And(App(J,x),No(P0,x)))
    u=fresh(X,'u');v=fresh(X,'v')
    fwd=gens([u,v],intro(apps(P0,u,v),lambda e:intro(App(J,u),lambda _:ar(mp(spec(Dom,u,v),ol(e,apps(Q,u,v)))))))
    def normal_of(a,ja):
        got=spec(mp(spec(wf_normal,P0),WP),a)
        t=fresh(X,'t');target=Ex(t,And(App(M,t),Star(P0,a,t)))
        def nft(t,h):
            jt=use(star_forward,[P0,J,a,t],[fwd,al(h),ja])
            return ei(target,t,ai(ai(jt,ar(h)),al(h)))
        return unpack(got,nft)
    nm=unpack(NJ,lambda a,ja:unpack(normal_of(a,ja),lambda t,h:ei(NE(M),t,al(h))))
    x=fresh(X,'x')
    def serial_at(mx):
        jx=al(mx);nx=ar(mx)
        def at_u(u,hu):
            ju=al(hu);e=ar(hu)
            qxu=cases(e,lambda pe:absurd(mp(spec(nx,u),pe),apps(Q,x,u)),lambda qe:qe)
            def at_t(t,ht):
                mt=al(ht);path=ar(ht);v=fresh(X,'v');w=fresh(X,'w')
                targetpred=Lam(v,apps(Q,x,v))
                def along(edge):
                    def qedge(qxv):
                        r=apply(spec(Route,x,v,w),qxv,edge)
                        def pcase(pp):
                            return unpack(pp,lambda z,h:absurd(mp(spec(nx,z),al(h)),apps(Q,x,w)))
                        return cases(r,pcase,lambda q:q)
                    return intro(apps(Q,x,v),qedge)
                advance=gens([v,w],intro(apps(P0,v,w),along))
                qxt=use(star_forward,[P0,targetpred,u,t],[advance,path,qxu])
                return ei(serial_target(Q,M,x),t,ai(mt,qxt))
            return unpack(normal_of(u,ju),at_t)
        return unpack(mp(spec(SJ,x),jx),at_u)
    sm=For(x,lambda x:intro(App(M,x),serial_at))
    bad=use(wf_no_serial,[Q,M],[WQ,nm,sm])
    return lemma('serial_binary_jumping_impossible',bad,[P0,Q,J],ass)
serial_binary=make_serial_binary()

def make_binary_wf():
    P0=fresh(Rel(X),'P');Q=fresh(Rel(X),'Q');E=Cup(P0,Q)
    ass=[WF(P0),WF(Q),BinaryRoute(P0,Q)]
    WP,WQ,Route=map(hyp,ass)
    def no_wf(nw):
        serialset=use(notwf_serial,[E],[nw])
        def withS(S,hs):
            J=PredClosure(E,S);nJ=use(closure_ne,[E,S],[al(hs)]);sJ=use(closure_serial,[E,S],[ar(hs)])
            bJ=spec(closure_back,E,S);Pc=Cut(J,P0);Qc=Cut(J,Q);Ec=Cup(Pc,Qc)
            x=fresh(X,'x');y=fresh(X,'y');z=fresh(X,'z')
            sp=gens([x,y],intro(apps(Pc,x,y),lambda h:al(ar(h))))
            sq=gens([x,y],intro(apps(Qc,x,y),lambda h:al(ar(h))))
            wpc=use(wf_mono,[Pc,P0],[sp,WP]);wqc=use(wf_mono,[Qc,Q],[sq,WQ])
            def getdom(h):
                return cases(h,lambda h:ai(al(h),ar(ar(h))),lambda h:ai(al(h),ar(ar(h))))
            dom=gens([x,y],intro(apps(Ec,x,y),getdom))
            def sx(jx):
                def at_y(y,hy):
                    jy=al(hy)
                    edge=cases(ar(hy),lambda p:ol(cproof(jx,p,jy),apps(Qc,x,y)),lambda q:ore(cproof(jx,q,jy),apps(Pc,x,y)))
                    return ei(serial_target(Ec,J,x),y,ai(jy,edge))
                return unpack(mp(spec(sJ,x),jx),at_y)
            ser=For(x,lambda x:intro(App(J,x),sx))
            u=fresh(X,'u');v=fresh(X,'v')
            bp=gens([u,v],intro(apps(P0,u,v),lambda e:intro(App(J,v),lambda jv:apply(spec(bJ,u,v),ol(e,apps(Q,u,v)),jv))))
            def route_q(qxy):
                def route_p(pyz):
                    jx=al(qxy);jz=ar(ar(pyz))
                    r=apply(spec(Route,x,y,z),al(ar(qxy)),al(ar(pyz)))
                    def pp(path):
                        def via(u,hu):
                            sc=use(star_cut,[P0,J,u,z],[bp,ar(hu),jz])
                            cutedge=cproof(jx,al(hu),al(sc))
                            return ol(ei(Plus(Pc,x,z),u,ai(cutedge,ar(sc))),apps(Qc,x,z))
                        return unpack(path,via)
                    return cases(r,pp,lambda q:ore(cproof(jx,q,jz),Plus(Pc,x,z)))
                return intro(apps(Pc,y,z),route_p)
            rc=gens([x,y,z],intro(apps(Qc,x,y),route_q))
            return use(serial_binary,[Pc,Qc,J],[wpc,wqc,dom,nJ,ser,rc])
        return unpack(serialset,withS)
    return lemma('binary_jumping_well_founded',by_contra(WF(E),no_wf),[P0,Q],ass)
binary_wf=make_binary_wf()

# A detour whose first edge is absent at the source cannot obstruct the final pair.
def AbsentDetourRoute(P0,Q,U,Vv):
    x=fresh(X,'x');y=fresh(X,'y');z=fresh(X,'z')
    return alls([x,y,z],imps([apps(Q,x,y),apps(P0,y,z)],Or(Detour(U,Vv,x,z),Or(Plus(P0,x,z),apps(Q,x,z)))))

def make_final_pair():
    P0=fresh(Rel(X),'P');Q=fresh(Rel(X),'Q');U=fresh(Rel(X),'U');Vv=fresh(Rel(X),'V');S=fresh(Arr(X,O),'S')
    ass=[WF(P0),WF(Q),AbsentDetourRoute(P0,Q,U,Vv),NoFrom(U,S),NE(S),serial(Cup(P0,Q),S)]
    WP,WQ,Route,NoU,NS,SS=map(hyp,ass)
    x=fresh(X,'x');y=fresh(X,'y');z=fresh(X,'z')
    Qgood=Lam(x,Lam(y,And(apps(Q,x,y),No(U,x))))
    sq=gens([x,y],intro(apps(Qgood,x,y),lambda h:al(h)))
    wq=use(wf_mono,[Qgood,Q],[sq,WQ])
    def rq(qxy):
        def rp(pyz):
            r=apply(spec(Route,x,y,z),al(qxy),pyz)
            def dcase(d):
                return unpack(d,lambda u,h:absurd(mp(spec(ar(qxy),u),al(h)),Or(Plus(P0,x,z),apps(Qgood,x,z))))
            def remaining(h):
                return cases(h,lambda p:ol(p,apps(Qgood,x,z)),lambda q:ore(ai(q,ar(qxy)),Plus(P0,x,z)))
            return cases(r,dcase,remaining)
        return intro(apps(P0,y,z),rp)
    rgood=gens([x,y,z],intro(apps(Qgood,x,y),rq))
    w=use(binary_wf,[P0,Qgood],[WP,wq,rgood])
    E=Cup(P0,Qgood)
    def sx(sx):
        def at_y(y,hy):
            e=cases(ar(hy),lambda p:ol(p,apps(Qgood,x,y)),lambda q:ore(ai(q,mp(spec(NoU,x),sx)),apps(P0,x,y)))
            return ei(serial_target(E,S,x),y,ai(al(hy),e))
        return unpack(mp(spec(SS,x),sx),at_y)
    ss=For(x,lambda x:intro(App(S,x),sx))
    return lemma('final_two_relations_no_branching_needed',use(wf_no_serial,[E,S],[w,NS,ss]),[P0,Q,U,Vv,S],ass)
final_pair=make_final_pair()


# The final pair and all internal indices are explicit in the statement.
def LastPair(Orel,pen,last):
    i=fresh(Idx,'i')
    return And(apps(Orel,pen,last),All(i,Or(Eq(i,last),Or(Eq(i,pen),apps(Orel,i,pen)))))

def Short(F,Orel,i):
    x=fresh(X,'x');y=fresh(X,'y');z=fresh(X,'z')
    R=Total(F);B=App(F,i);P0=Part(F,Orel,i,True);T=Part(F,Orel,i)
    return alls([x,y,z],imps([apps(T,x,y),apps(B,y,z)],Or(Detour(P0,R,x,z),Plus(B,x,z))))

def InternalBranching(F,Orel,zero,pen):
    i=fresh(Idx,'i')
    return All(i,imps([Not(Eq(i,zero)),apps(Orel,i,pen)],And(FB(App(F,i)),Short(F,Orel,i))))

def Active(F,S):
    i=fresh(Idx,'i');x=fresh(X,'x');z=fresh(X,'z')
    return Lam(i,Exists([x,z],And(App(S,x),apps(F,i,x,z))))

def active_member(F,S,i,x,z,sx,e):
    f=norm(App(Active(F,S),i));inner=norm(subst(f[2],f[1],x))
    return ei(f,x,ei(inner,z,ai(sx,e)))

def CoversActive(F,S,Vv):
    i=fresh(Idx,'i');x=fresh(X,'x');z=fresh(X,'z')
    return alls([i,x,z],imps([App(S,x),apps(F,i,x,z)],App(Vv,i)))

def make_tail_pair_exact():
    F=fresh(FamTy,'F');Orel=fresh(Rel(Idx),'order');pen=fresh(Idx,'pen');last=fresh(Idx,'last');x=fresh(X,'x');y=fresh(X,'y')
    ass=[irrefl(Orel),trans(Orel),LastPair(Orel,pen,last),apps(Part(F,Orel,pen),x,y)]
    IR,TR,LP,Txy=map(hyp,ass)
    def atj(j,h):
        pij=al(h);edge=ar(h);k=fresh(Idx,'k')
        def islast(eq):return eq_transport(eq,Lam(k,apps(F,k,x,y)),edge)
        def other(hh):
            def ispen(eq):
                pii=eq_transport(eq,Lam(k,apps(Orel,pen,k)),pij)
                return absurd(mp(spec(IR,pen),pii),apps(F,last,x,y))
            def before(jp):
                cyc=apply(spec(TR,pen,j,pen),pij,jp)
                return absurd(mp(spec(IR,pen),cyc),apps(F,last,x,y))
            return cases(hh,ispen,before)
        return cases(spec(ar(LP),j),islast,other)
    return lemma('tail_at_penultimate_is_last',unpack(Txy,atj),[F,Orel,pen,last,x,y],ass)
tail_pair_exact=make_tail_pair_exact()

# Core contradiction on an arbitrary serial domain; only the index set is finite.
def make_family_branching_core():
    F=fresh(FamTy,'F');Orel=fresh(Rel(Idx),'order');zero=fresh(Idx,'zero');pen=fresh(Idx,'pen');last=fresh(Idx,'last')
    J=fresh(Arr(X,O),'J');CK=fresh(Arr(Idx,O),'coverK');R=Total(F);A=App(F,zero)
    x=fresh(X,'x');M=Lam(x,And(App(J,x),No(A,x)));i=fresh(Idx,'i')
    allK=All(i,App(CK,i))
    ass=[Fin(CK),allK,irrefl(Orel),trans(Orel),tri(Orel),least(Orel,zero),LastPair(Orel,pen,last),WFcolors(F),Gzero(F,Orel,zero),Gothers(F,Orel,zero),InternalBranching(F,Orel,zero,pen),domain(R,J),NE(J),serial(R,J)]
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
                    data=apply(spec(IB,i),nz,ipen);fb=al(data);short=ar(data)
                    x=fresh(X,'x');y=fresh(X,'y');z=fresh(X,'z');k=fresh(Idx,'k')
                    def sx(sx):
                        def sy(sy):
                            def rx(rxy):
                                def bz(byz):
                                    def atj(j,e):
                                        def equal(eq):
                                            bxy=eq_transport(eq,Lam(k,apps(F,k,x,y)),e)
                                            return use(plus_cons,[B,x,y,z],[bxy,use(plus_one,[B,y,z],[byz])])
                                        def other(h):
                                            def before(ji):return absurd(block(j,x,y,ji,sx,e),Plus(B,x,z))
                                            def later(ij):
                                                tx=ei(norm(apps(Part(F,Orel,i),x,y)),j,ai(ij,e))
                                                routed=apply(spec(short,x,y,z),tx,byz)
                                                def det(d):return unpack(d,lambda u,h:absurd(blockp(x,u,sx,al(h)),Plus(B,x,z)))
                                                return cases(routed,det,lambda p:p)
                                            return cases(h,before,later)
                                        return cases(spec(OTT,j,i),equal,other)
                                    return unpack(rxy,atj)
                                return intro(apps(B,y,z),bz)
                            return intro(apps(R,x,y),rx)
                        return intro(App(S,y),sy)
                    route=gens([x,y,z],intro(App(S,x),sx))
                    x=fresh(X,'x');y=fresh(X,'y')
                    br=gens([x,y],intro(apps(B,x,y),lambda e:use(color_total,[F,i,x,y],[e])))
                    sjall=For(x,lambda x:intro(App(S,x),lambda h:sj(x,h)))
                    cleared=use(clear_branching,[R,B,J,S],[irR,spec(WFC,i),br,DJ,sjall,NS,RS,route,fb])
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
    return lemma('serial_domain_arbitrary_family_branching_impossible',unpack(minima,atV),[F,Orel,zero,pen,last,J,CK],ass)
branching_core=make_family_branching_core()


# The branching assumptions and shortened conditions survive restriction.
def make_cut_fb():
    B=fresh(Rel(X),'B');J=fresh(Arr(X,O),'J');x=fresh(X,'x');y=fresh(X,'y')
    BC=Cut(J,B)
    def atx(x):
        def atc(C,hc):
            cv=For(y,lambda y:intro(apps(BC,x,y),lambda h:mp(spec(ar(hc),y),al(ar(h)))))
            return ei(FC(Lam(y,apps(BC,x,y))),C,ai(al(hc),cv))
        return unpack(spec(hyp(FB(B)),x),atc)
    return lemma('finite_branching_preserved_by_restriction',For(x,atx),[B,J],[FB(B)])
cut_fb=make_cut_fb()

def make_cut_short():
    F=fresh(FamTy,'F');J=fresh(Arr(X,O),'J');Orel=fresh(Rel(Idx),'order');i=fresh(Idx,'i')
    R=Total(F);CF=CutFamily(J,F);RC=Total(CF);B=App(F,i);BC=App(CF,i)
    T=Part(F,Orel,i);TC=Part(CF,Orel,i);P0=Part(F,Orel,i,True);PC=Part(CF,Orel,i,True)
    ass=[backward(R,J),Short(F,Orel,i)];Back,Sht=map(hyp,ass)
    x=fresh(X,'x');y=fresh(X,'y');z=fresh(X,'z')
    def late(tcut):
        endpoints=use(cut_tail_out,[F,J,Orel,i,x,y],[tcut]);jx=al(endpoints);oldtail=al(ar(endpoints))
        def edge(bcut):
            jz=ar(ar(bcut));r=apply(spec(Sht,x,y,z),oldtail,al(ar(bcut)))
            def det(d):
                def at_u(u,h):
                    path=use(star_family_cut,[F,J,u,z],[Back,ar(h),jz])
                    prior=use(cut_early_in,[F,J,Orel,i,x,u],[jx,al(h),al(path)])
                    dc=ei(Detour(PC,RC,x,z),u,ai(prior,ar(path)))
                    return ol(dc,Plus(BC,x,z))
                return unpack(d,at_u)
            def samecol(p):
                pc=ar(use(plus_family_cut,[F,J,i,x,z],[Back,p,jz]))
                return ore(pc,Detour(PC,RC,x,z))
            return cases(r,det,samecol)
        return intro(apps(BC,y,z),edge)
    return lemma('shortened_conditions_preserved_by_restriction',gens([x,y,z],intro(apps(TC,x,y),late)),[F,J,Orel,i],ass)
cut_short=make_cut_short()

def make_cut_internal():
    F=fresh(FamTy,'F');J=fresh(Arr(X,O),'J');Orel=fresh(Rel(Idx),'order');zero=fresh(Idx,'zero');pen=fresh(Idx,'pen')
    ass=[backward(Total(F),J),InternalBranching(F,Orel,zero,pen)];Back,IB=map(hyp,ass)
    i=fresh(Idx,'i')
    def at_i(nz):
        def before(ip):
            info=apply(spec(IB,i),nz,ip)
            b=use(cut_fb,[App(F,i),J],[al(info)])
            s=use(cut_short,[F,J,Orel,i],[Back,ar(info)])
            return ai(b,s)
        return intro(apps(Orel,i,pen),before)
    return lemma('internal_branching_data_preserved_by_restriction',For(i,lambda i:intro(Not(Eq(i,zero)),at_i)),[F,J,Orel,zero,pen],ass)
cut_internal=make_cut_internal()

# Main branching theorem: arbitrary finite index set, unrestricted carrier X.
def make_full_branching():
    F=fresh(FamTy,'F');Orel=fresh(Rel(Idx),'order');zero=fresh(Idx,'zero');pen=fresh(Idx,'pen');last=fresh(Idx,'last')
    ass=[FinType(Idx),irrefl(Orel),trans(Orel),tri(Orel),least(Orel,zero),LastPair(Orel,pen,last),WFcolors(F),Gzero(F,Orel,zero),Gothers(F,Orel,zero),InternalBranching(F,Orel,zero,pen)]
    FK,OI,OT,OTT,LZ,LP,WFC,G0,Gi,IB=map(hyp,ass);R=Total(F)
    def notwf(nw):
        serialset=use(notwf_serial,[R],[nw])
        def atS(S,hs):
            J=PredClosure(R,S);CF=CutFamily(J,F)
            NJ=use(closure_ne,[R,S],[al(hs)]);SJ=use(closure_serial,[R,S],[ar(hs)])
            BJ=spec(closure_back,R,S)
            wc=use(cut_wf,[F,J],[WFC]);dc=spec(cut_domain,F,J);sc=use(cut_serial,[F,J],[SJ])
            g0=use(cut_gzero,[F,J,Orel,zero],[BJ,G0]);gi=use(cut_gothers,[F,J,Orel,zero],[BJ,Gi]);ib=use(cut_internal,[F,J,Orel,zero,pen],[BJ,IB])
            return unpack(FK,lambda CK,hk:use(branching_core,[CF,Orel,zero,pen,last,J,CK],[al(hk),ar(hk),OI,OT,OTT,LZ,LP,wc,g0,gi,ib,dc,NJ,sc]))
        return unpack(serialset,atS)
    return lemma('arbitrary_finite_family_branching_termination',by_contra(WF(R),notwf),[F,Orel,zero,pen,last],ass)
main_branching=make_full_branching()

# No infinite forward chain: this is a consequence of the checked induction principle.
def make_nochain_branching():
    F=fresh(FamTy,'F');Orel=fresh(Rel(Idx),'order');zero=fresh(Idx,'zero');pen=fresh(Idx,'pen');last=fresh(Idx,'last')
    ass=[FinType(Idx),irrefl(Orel),trans(Orel),tri(Orel),least(Orel,zero),LastPair(Orel,pen,last),WFcolors(F),Gzero(F,Orel,zero),Gothers(F,Orel,zero),InternalBranching(F,Orel,zero,pen)]
    W=use(main_branching,[F,Orel,zero,pen,last],list(map(hyp,ass)))
    N='N';f=fresh(Arr(N,X),'f');s=fresh(Arr(N,N),'next');a=fresh(N,'start');n=fresh(N,'n')
    chain=All(n,apps(Total(F),App(f,n),App(f,App(s,n))))
    no=ii(chain,use(wf_no_chain,[Total(F),f,s,a],[W,hyp(chain)]))
    return lemma('branching_termination_excludes_infinite_forward_chains',gens([f,s,a],no),[F,Orel,zero,pen,last],ass)
branching_nochain=make_nochain_branching()


# Concise public statement: shortened conditions internally; full condition only
# at the penultimate index. No redundant full conditions are assumed internally.
def FullAt(F,Orel,i):
    x=fresh(X,'x');y=fresh(X,'y');z=fresh(X,'z');R=Total(F)
    return alls([x,y,z],imps([apps(Part(F,Orel,i),x,y),apps(F,i,y,z)],
        Or(Detour(Part(F,Orel,i,True),R,x,z),Or(Plus(App(F,i),x,z),apps(Part(F,Orel,i),x,z)))))

def make_complete_branch_conditions():
    F=fresh(FamTy,'F');Orel=fresh(Rel(Idx),'order');zero=fresh(Idx,'zero');pen=fresh(Idx,'pen');last=fresh(Idx,'last')
    ass=[irrefl(Orel),trans(Orel),LastPair(Orel,pen,last),FullAt(F,Orel,pen),InternalBranching(F,Orel,zero,pen)]
    IR,TR,LP,Final,Internal=map(hyp,ass)
    i=fresh(Idx,'i');x=fresh(X,'x');y=fresh(X,'y');z=fresh(X,'z');k=fresh(Idx,'k')
    def at_i(nz):
        def at_tail(txy):
            def at_edge(byz):
                target=Or(Detour(Part(F,Orel,i,True),Total(F),x,z),Or(Plus(App(F,i),x,z),apps(Part(F,Orel,i),x,z)))
                def islast(eq):
                    def atj(j,hj):
                        lj=eq_transport(eq,Lam(k,apps(Orel,k,j)),al(hj))
                        def eql(eqj):
                            ll=eq_transport(eqj,Lam(k,apps(Orel,last,k)),lj)
                            return mp(spec(IR,last),ll)
                        def rest(h):
                            def eqp(eqp):
                                lp=eq_transport(eqp,Lam(k,apps(Orel,last,k)),lj)
                                ll=apply(spec(TR,last,pen,last),lp,al(LP))
                                return mp(spec(IR,last),ll)
                            def jp(jp):
                                lp=apply(spec(TR,last,j,pen),lj,jp)
                                ll=apply(spec(TR,last,pen,last),lp,al(LP))
                                return mp(spec(IR,last),ll)
                            return cases(h,eqp,jp)
                        return cases(spec(ar(LP),j),eql,rest)
                    return absurd(unpack(txy,atj),target)
                def ispen(eq):
                    rev=use(inst(eq_sym,X=Idx),[i,pen],[eq])
                    instfinal=eq_transport(rev,Lam(k,FullAt(F,Orel,k)),Final)
                    return apply(spec(instfinal,x,y,z),txy,byz)
                def internal(ip):
                    data=apply(spec(Internal,i),nz,ip)
                    r=apply(spec(ar(data),x,y,z),txy,byz)
                    return cases(r,lambda d:ol(d,Or(Plus(App(F,i),x,z),apps(Part(F,Orel,i),x,z))),
                        lambda p:ore(ol(p,apps(Part(F,Orel,i),x,z)),Detour(Part(F,Orel,i,True),Total(F),x,z)))
                return cases(spec(ar(LP),i),islast,lambda h:cases(h,ispen,internal))
            return intro(apps(F,i,y,z),at_edge)
        return intro(apps(Part(F,Orel,i),x,y),at_tail)
    return lemma('shortened_internal_and_final_conditions_suffice',gens([i,x,y,z],intro(Not(Eq(i,zero)),at_i)),[F,Orel,zero,pen,last],ass)
complete_conditions=make_complete_branch_conditions()

def make_public_branching():
    F=fresh(FamTy,'F');Orel=fresh(Rel(Idx),'order');zero=fresh(Idx,'zero');pen=fresh(Idx,'pen');last=fresh(Idx,'last')
    ass=[FinType(Idx),irrefl(Orel),trans(Orel),tri(Orel),least(Orel,zero),LastPair(Orel,pen,last),WFcolors(F),Gzero(F,Orel,zero),FullAt(F,Orel,pen),InternalBranching(F,Orel,zero,pen)]
    hs=list(map(hyp,ass))
    gi=use(complete_conditions,[F,Orel,zero,pen,last],[hs[1],hs[2],hs[5],hs[8],hs[9]])
    out=use(main_branching,[F,Orel,zero,pen,last],hs[:8]+[gi,hs[9]])
    return lemma('finitely_branching_internal_relations_terminate',out,[F,Orel,zero,pen,last],ass)
public_branching=make_public_branching()

# Preserve both the finite-domain and finite-branching theorems and dependencies.
save_certificate(K, THEOREMS, 'proof.json')
print('COMBINED CERTIFICATE:', len(K.records), 'inferences;', len(THEOREMS), 'closed named theorems')
