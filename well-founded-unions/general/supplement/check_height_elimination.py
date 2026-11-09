#!/usr/bin/env python3
"""Finite regression check of representative-preserving height elimination.
This is not a proof for arbitrary domains and is not a Rocq kernel check.
Only Python's standard library is used. Failures are explicit, not assertions.
"""
import json
from pathlib import Path

def require(p, message):
    if not p:
        raise RuntimeError(message)

def closure(q, n):
    r = set(q)
    for k in range(n):
        r |= {(i,j) for i in range(n) for j in range(n)
              if (i,k) in r and (k,j) in r}
    return r

def representatives(k, s, n):
    return all(any(all((x,z) not in k or (x,t) in k for x in s)
                   for t in s) for z in range(n))

def heights(q, n):
    h = [0]*n
    for _ in range(n):
        h = [max((1+h[y] for y in range(n) if (x,y) in q), default=0)
             for x in range(n)]
    return h

def check(n=3):
    edges=[(x,y) for x in range(n) for y in range(n) if x != y]
    graphs=[{e for j,e in enumerate(edges) if mask>>j&1}
            for mask in range(1<<len(edges))]
    dags=[q for q in graphs if not any((x,x) in closure(q,n) for x in range(n))]
    sources=[{x for x in range(n) if mask>>x&1} for mask in range(1,1<<n)]
    applicable=rounds=strong=0
    for k in graphs:
        for q in dags:
            if not q<=k: continue
            qp=closure(q,n)
            h=heights(q,n)
            for s0 in sources:
                if not representatives(k,s0,n): continue
                if not all((x,z) in qp or (x,z) in k
                           for x in s0 for y in s0 for z in range(n)
                           if (x,y) in k-q and (y,z) in q):
                    continue
                applicable += 1
                s=set(s0)
                while max(h[x] for x in s)>0:
                    H=max(h[x] for x in s)
                    u={x for x in s if h[x]==H}
                    dom={(x,y) for x in s for y in s if (x,y) in k and
                         all((a,x) not in k or (a,y) in k for a in s)}
                    require(all((x,z) in dom for x,y in dom for a,z in dom if y==a),
                            'domination not transitive')
                    require(not any((x,x) in closure(dom,n) for x in s),
                            'cyclic domination')
                    for y in u:
                        require(any((y,t) in dom for t in s), 'missing top-level successor')
                    s-=u
                    require(bool(s), 'height elimination emptied representative set')
                    require(representatives(k,s,n), 'lost representatives')
                    require(max(h[x] for x in s)<H, 'height bound did not decrease')
                    rounds+=1
                require(not any(x in s for x,y in q), 'outgoing Q edge remains')
                if all((x,z) in qp for x in s0 for y in s0 for z in range(n)
                       if (x,y) in k-q and (y,z) in q):
                    strong+=1
                    require(all(h[y]<=h[x] for x in s0 for y in s0 if (x,y) in k),
                            'strong-condition height propagation failed')
    return dict(vertices=n,irreflexive_relations=len(graphs),acyclic_relations=len(dags),
                applicable_settings=applicable,elimination_rounds=rounds,
                strong_condition_settings=strong,status='passed',
                scope='exhaustive three-point regression; not an arbitrary-domain proof')

if __name__=='__main__':
    result=check()
    print(json.dumps(result,indent=2))
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
