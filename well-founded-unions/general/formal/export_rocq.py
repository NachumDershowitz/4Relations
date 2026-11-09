"""Export the checked natural-deduction DAG as explicit Rocq proof terms.
The exporter is not trusted: proof.json is checked independently of this file.
No tactic search, admission or added mathematical axiom occurs in the export.
"""
import contextlib,io
import kernel as k
with contextlib.redirect_stdout(io.StringIO()):
    K,data=k.load_and_check('proof.json')

supports=[]
for r,refs,args in K.records:
    sets=[supports[i] for i in refs]
    if r in ('assume','em'):s=set(k.fv(args[0]))
    elif r=='all_i':s=set(sets[0])-{args[0]}
    elif r=='ex_e':s=set(sets[0])|(set(sets[1])-{args[0]})
    elif r=='type_inst':
        m=dict(args[0]);s={k.V(v[1],k.ty_sub(v[2],m)) for v in sets[0]}
    else:
        s=set().union(*sets)
        for a in args:s.update(k.fv(a))
    supports.append(frozenset(s))
for name,(i,_) in data['theorems'].items():
    extra=supports[i]-k.fv(K.proofs[i].conclusion)
    if extra:print('EXTRA PROOF PARAMETERS',name,extra)

# Stable function parameters. Only the proof's actual free variables are bound.
def typevars(t):
    if isinstance(t,str):return set() if t=='o' else {t}
    return typevars(t[1])|typevars(t[2])
def termtypes(t):
    if t[0]=='v':return typevars(t[2])
    if t[0]=='bot':return set()
    return termtypes(t[1])|termtypes(t[2])
metadata=[]
for i,j in enumerate(K.proofs):
    vs=sorted(supports[i],key=repr)
    tv=termtypes(j.conclusion)
    for h in j.assumptions:tv|=termtypes(h)
    for v in vs:tv|=typevars(v[2])
    # Prior nodes may use a type parametrically even if absent from their result.
    r,refs,args=K.records[i]
    for rid in refs:
        m=dict(args[0]) if r=='type_inst' else {}
        for t in metadata[rid][0]:tv|=typevars(k.ty_sub(t,m))
    metadata.append((sorted(tv),vs))

def ty(t):
    if isinstance(t,str):return 'Prop' if t=='o' else t
    return '('+ty(t[1])+' -> '+ty(t[2])+')'

counter=0
def ident(prefix):
    global counter
    counter+=1;return prefix+str(counter)

def render(t,env):
    tag=t[0]
    if tag=='v':
        if t not in env:raise RuntimeError('unbound exporter variable '+str(t))
        return env[t]
    if tag=='bot':return 'False'
    if tag=='app':return '('+render(t[1],env)+' '+render(t[2],env)+')'
    if tag in ('lam','all','ex'):
        v,b=t[1:];name=ident('b');en=dict(env);en[v]=name
        kw={'lam':'fun','all':'forall','ex':'exists'}[tag];sep=' => ' if tag=='lam' else ', '
        return '('+kw+' ('+name+' : '+ty(v[2])+')'+sep+render(b,en)+')'
    op={'imp':' -> ','and':' /\\ ','or':' \\/ '}[tag]
    return '('+render(t[1],env)+op+render(t[2],env)+')'

def hkey(t):return k.key(t)

def reference(i,env,hyps,m=None):
    m=m or {};tv,vs=metadata[i]
    ts=[ty(k.ty_sub(t,m)) for t in tv]
    vals=[]
    for v in vs:
        vv=k.V(v[1],k.ty_sub(v[2],m))
        if vv not in env:raise RuntimeError('missing reference parameter '+str((i,vv)))
        vals.append(env[vv])
    hs=[]
    for a in K.proofs[i].assumptions:
        a=k.type_sub(a,m) if m else a
        ky=hkey(a)
        if ky not in hyps:raise RuntimeError('missing reference hypothesis '+str(i))
        hs.append(hyps[ky])
    return '(@proof_'+str(i)+' '+ ' '.join(ts+vals+hs)+')'

def proofbody(i,env,hyps):
    r,ids,a=K.records[i];ps=[K.proofs[j] for j in ids]
    def ref(j,en=env,hs=hyps,m=None):return reference(ids[j],en,hs,m)
    def tm(t):return render(t,env)
    if r=='assume':return hyps[hkey(a[0])]
    if r=='imp_i':
        n=ident('h');hs=dict(hyps);hs[hkey(a[0])]=n
        return '(fun ('+n+' : '+tm(a[0])+') => '+ref(0,env,hs)+')'
    if r=='imp_e':return '('+ref(0)+' '+ref(1)+')'
    if r=='and_i':return '(@conj '+tm(ps[0].conclusion)+' '+tm(ps[1].conclusion)+' '+ref(0)+' '+ref(1)+')'
    if r in ('and_l','and_r'):
        f=k.norm(ps[0].conclusion);return '(@'+('proj1' if r=='and_l' else 'proj2')+' '+tm(f[1])+' '+tm(f[2])+' '+ref(0)+')'
    if r in ('or_l','or_r'):
        A,B=(ps[0].conclusion,a[0]) if r=='or_l' else (a[0],ps[0].conclusion)
        return '(@'+('or_introl' if r=='or_l' else 'or_intror')+' '+tm(A)+' '+tm(B)+' '+ref(0)+')'
    if r=='or_e':
        f=k.norm(ps[0].conclusion);cases=[]
        for j in (1,2):
            n=ident('h');hs=dict(hyps);hs[hkey(f[j])]=n
            cases.append('(fun ('+n+' : '+tm(f[j])+') => '+ref(j,env,hs)+')')
        return '(@or_ind '+tm(f[1])+' '+tm(f[2])+' '+tm(ps[1].conclusion)+' '+' '.join(cases)+' '+ref(0)+')'
    if r=='all_i':
        v=a[0];n=ident('v');en=dict(env);en[v]=n
        return '(fun ('+n+' : '+ty(v[2])+') => '+ref(0,en,hyps)+')'
    if r=='all_e':return '('+ref(0)+' '+tm(a[0])+')'
    if r=='ex_i':
        f,w=a;v,b=f[1:];pred=render(k.Lam(v,b),env)
        return '(@ex_intro '+ty(v[2])+' '+pred+' '+tm(w)+' '+ref(0)+')'
    if r=='ex_e':
        f=k.norm(ps[0].conclusion);v=a[0];n=ident('v');hn=ident('h');en=dict(env);en[v]=n
        witness_hyp=k.subst(f[2],f[1],v);hs=dict(hyps);hs[hkey(witness_hyp)]=hn
        branch='(fun ('+n+' : '+ty(v[2])+') ('+hn+' : '+render(witness_hyp,en)+') => '+ref(1,en,hs)+')'
        return '(@ex_ind '+ty(v[2])+' '+render(k.Lam(f[1],f[2]),env)+' '+tm(ps[1].conclusion)+' '+branch+' '+ref(0)+')'
    if r=='false_e':return '(@False_ind '+tm(a[0])+' '+ref(0)+')'
    if r=='em':return '(@classic '+tm(a[0])+')'
    if r=='conv':return ref(0)
    if r=='type_inst':return ref(0,m=dict(a[0]))
    raise RuntimeError(r)

with open('WellFoundedUnionsProofTerms.v','w') as out:
    out.write('''(* Explicit proof-term export of proof.json.
   Checked locally by the two supplied higher-order-logic certificate checkers.
   This .v export has NOT been compiled with Rocq in this environment.
   The only logical axiom used is classical excluded middle.
*)
From Stdlib Require Import Logic.Classical_Prop.
Set Universe Polymorphism.
Unset Implicit Arguments.

''')
    for i,j in enumerate(K.proofs):
        tv,vs=metadata[i];env={v:'v'+str(n) for n,v in enumerate(vs)}
        hyps={hkey(a):'h'+str(n) for n,a in enumerate(j.assumptions)}
        params=['('+t+' : Type)' for t in tv]
        params+=['('+env[v]+' : '+ty(v[2])+')' for v in vs]
        params+=['('+hyps[hkey(a)]+' : '+render(a,env)+')' for a in j.assumptions]
        out.write('Definition proof_'+str(i)+' '+' '.join(params)+'\n  : '+render(j.conclusion,env)+'\n  := '+proofbody(i,env,hyps)+'.\nOpaque proof_'+str(i)+'.\n\n')
    for name,(i,_) in data['theorems'].items():
        out.write('Definition '+name+' := @proof_'+str(i)+'.\n')
    for name in ['arbitrary_finite_family_well_founded_union', 'arbitrary_finite_acyclic_family_termination', 'well_founded_finitely_branching_finite_reachability', 'finitely_branching_internal_relations_terminate', 'arbitrary_finite_family_branching_termination', 'branching_termination_excludes_infinite_forward_chains', 'arbitrary_finite_acyclic_family_has_acyclic_union', 'arbitrary_family_mixed_height_termination', 'arbitrary_family_limit_rank_obstruction', 'zero_or_successor_internal_ranks_imply_termination', 'arbitrary_family_mixed_height_and_ordinal_termination']:
        out.write('Print Assumptions '+name+'.\n')
print('Wrote WellFoundedUnionsProofTerms.v (explicit terms; no proof-search tactics).')
