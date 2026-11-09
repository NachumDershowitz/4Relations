"""Finite sanity checks for the reset-system section; not an infinite proof."""
from __future__ import annotations
import json
from itertools import product
from pathlib import Path

State = tuple[str, int, int]

def edge(c: str, x: State, y: State) -> bool:
    mode, m, n = x
    dest, i, j = y
    if c == 'A': return mode == dest == 'q' and (i, j) < (m, n)
    if c == 'B': return mode == 'p' and dest == 'q' and (i, j) == (n, 2**m)
    if c == 'C': return mode == 'q' and dest == 'p' and (j, 2**i) < (m, n)
    if c == 'D': return mode == 'p' and dest == 'q' and (i, j) < (n, 2**m)
    raise ValueError(c)

def rank(x: State) -> tuple[int, int]:
    mode, m, n = x
    return (m, 2*n) if mode == 'q' else (n, 2**(m+1)+1)

states: list[State] = [(s,m,n) for s in ('p','q') for m,n in product(range(9), repeat=2)]
adj = {c: {x: [y for y in states if edge(c,x,y)] for x in states} for c in 'ABCD'}
counts: dict[str, int] = {}
for c in 'ABCD':
    counts[f'{c}_rank_edges'] = 0
    for x in states:
        for y in adj[c][x]:
            assert rank(x) > rank(y), (c,x,y)
            counts[f'{c}_rank_edges'] += 1
# B-images beyond the box are checked directly as well.
for x in states:
    if x[0]=='p':
        y=('q',x[2],2**x[1])
        assert edge('B',x,y) and rank(x)>rank(y)
        assert y[0]!='p'

for label, first, second in [('EA','BCD','A'), ('FB','CD','B'), ('DC','D','C'), ('UV','AC','BD')]:
    counts[label+'_paths'] = 0
    for c in first:
        for d in second:
            for x in states:
                for y in adj[c][x]:
                    for z in adj[d][y]:
                        if label=='EA': assert edge('D',x,z), (x,y,z)
                        elif label in ('FB','UV'): assert edge('A',x,z), (x,y,z)
                        else:
                            witness=('q',x[2],2**x[1])
                            assert edge('B',x,witness) and edge('C',witness,z), (x,y,z)
                        counts[label+'_paths'] += 1

for x in states:
    for z in adj['D'][x]:
        witness=('q',x[2],2**x[1])
        assert edge('B',x,witness) and edge('A',witness,z)

for n in range(11):
    run: list[State] = [('p',3,2),('q',2,8),('q',2,7),('p',2,2),('q',2,3),('p',n,1),('q',1,2**n)]
    run += [('q',1,j) for j in range(2**n-1,-1,-1)]
    labels='BACDCB'+'A'*(2**n)
    assert len(run)-1==2**n+6==len(labels)
    for x,y,c in zip(run,run[1:],labels):
        assert edge(c,x,y), (n,c,x,y)
        assert rank(x)>rank(y)
    assert edge('A',run[-1],('q',0,0))

x,y,u,z=('p',2,0),('q',0,3),('q',0,4),('p',1,0)
for c,a,b in [('D',x,y),('C',y,z),('B',x,u),('C',u,z),('A',u,y)]:
    assert edge(c,a,b), (c,a,b)
assert not edge('D',x,z)
assert x[0]=='p'  # C has only q-sources, so C(C union D)* cannot connect x to z.

report={
 'sample_register_bounds':[0,8],
 'state_count':len(states),
 'tested_paths_and_edges':counts,
 'run_parameters_checked':[0,10],
 'figure_edges_checked':5,
 'all_checks_passed':True,
 'scope':'Finite sanity checks only. The section gives the general mathematical proofs; no proof assistant was run.'
}
Path(__file__).with_name('reset_checks.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
