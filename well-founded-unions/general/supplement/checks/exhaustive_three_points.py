"""Exhaustive diagnostic check of the finite projection/elimination lemma.

All 25 acyclic A, all 25 acyclic B, and all 64 irreflexive F on three
labeled points are considered. The check uses only the relaxed sink-row
forms of P0 and P1, not Q2 or a decomposition of F into two colors.
"""
from __future__ import annotations
from itertools import product
from pathlib import Path
import json


def require(condition: bool, message: str) -> None:
    """Keep diagnostic checks active even with Python's -O flag."""
    if not condition:
        raise RuntimeError(message)


def closure(p: set[tuple[int,int]], n: int) -> set[tuple[int,int]]:
    q=set(p)
    for k in range(n):
        q |= {(i,j) for i in range(n) for j in range(n) if (i,k) in q and (k,j) in q}
    return q


def eliminate(A, B, F, n):
    V=set(range(n)); E=B|F
    Ap=closure(A,n); Bp=closure(B,n)
    S={x for x in V if not any(a==x for a,b in A)}
    pi={z:min(t for t in S if t==z or (z,t) in Ap) for z in V}
    steps=[]
    def invariant():
        require(bool(S) and set(pi.values()) <= S, "Empty or invalid representative range")
        require(all(pi[x] == x for x in S), "Projection is not the identity on its range")
        require(all((x, pi[z]) in E for x, z in E if x in S), "Incoming-edge invariant failed")
        require(all(any((x, y) in E for y in S) for x in S), "E is not serial on the range")
    invariant()
    while True:
        targets={z for x,z in B if x in S}
        if not targets:
            require(all((x, y) not in B for x in S for y in V), "A B-target remains")
            require(all(any((x, y) in F for y in S) for x in S), "Terminal F is not serial")
            require(any((x, x) in closure(F & set(product(S, S)), n) for x in S), "Terminal F has no cycle")
            return steps,S
        z=min(z for z in targets if not any((w,z) in Bp for w in targets))
        Y={y for y in S if (y,z) in B}
        t=pi[z]
        require(bool(Y) and t not in Y, "Invalid deletion/replacement pair")
        # Domain-independent one-step implication.
        require(all((x, z) in E for x in S for y in Y if (x, y) in E), "Fold transfer failed")
        pi={v:t if pi[v] in Y else pi[v] for v in V}
        S-=Y
        steps.append({'target':z,'removed':sorted(Y),'replacement':t,'remaining':sorted(S)})
        invariant()


def main():
    n=3;V=set(range(n));edges=[(x,y) for x in V for y in V if x!=y]
    rels=[{e for k,e in enumerate(edges) if mask>>k&1} for mask in range(1<<len(edges))]
    dags=[(P,closure(P,n)) for P in rels if not any((x,x) in closure(P,n) for x in V)]
    checked=valid=with_folds=max_folds=0;example=None
    for (A,Ap),(B,Bp),F in product(dags,dags,rels):
        checked+=1;E=B|F;R=A|E
        if not all(any((x,y) in R for y in V) for x in V):continue
        S={x for x in V if not any((x,y) in A for y in V)}
        if any((x,z) not in E for x,y in E for v,z in A if y==v and x in S):continue
        if any((x,z) not in Bp|F for x,y in F for v,z in B if y==v and x in S):continue
        steps,terminal=eliminate(A,B,F,n);valid+=1
        if steps:
            with_folds+=1
            if example is None:example={'A':sorted(A),'B':sorted(B),'F':sorted(F),'steps':steps,'terminal':sorted(terminal)}
        max_folds=max(max_folds,len(steps))
    record={'points':n,'acyclic_relations':len(dags),'irreflexive_F':len(rels),'triples_tested':checked,
            'triples_satisfying_relaxed_premises':valid,'triples_requiring_folds':with_folds,
            'maximum_folds':max_folds,'all_invariants_passed':True,'example':example}
    out=Path(__file__).parent/'folding_checks'/'exhaustive_three_points.json'
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(record,indent=2))

if __name__=='__main__':main()
