#!/usr/bin/env python3
"""Exhaust all four individually acyclic relations on at most three points.

This is a finite sanity check, not a proof of the general theorem. Every
relation may overlap the other colors. Composition is left-to-right.
"""
from __future__ import annotations
from itertools import product
from pathlib import Path
import json
import time


def run(n: int) -> dict:
    start = time.monotonic()
    size = 1 << (n * n)
    ident = sum(1 << (i*n+i) for i in range(n))

    def compose(p: int, q: int) -> int:
        ans = 0
        for i in range(n):
            for j in range(n):
                if p & (1 << (i*n+j)):
                    ans |= ((q >> (j*n)) & ((1 << n)-1)) << (i*n)
        return ans

    products = [[compose(p, q) for q in range(size)] for p in range(size)]
    plus = []
    for r in range(size):
        closure = r
        while True:
            new = closure | products[closure][r]
            if new == closure:
                break
            closure = new
        plus.append(closure)
    dags = [r for r in range(size) if not (plus[r] & ident)]
    tested = premises = strong_premises = 0
    counterexamples = []
    for a, b, c, d in product(dags, repeat=4):
        tested += 1
        f = c | d
        e = b | f
        r = a | e
        ar = products[a][plus[r] | ident]
        if products[e][a] & ~(ar | e):
            continue
        fb = products[f][b]
        if fb & ~(ar | plus[b] | f):
            continue
        if products[d][c] & ~(products[b][plus[e] | ident] | plus[c] | d):
            continue
        premises += 1
        if not (fb & ~(ar | plus[b])):
            strong_premises += 1
        if plus[r] & ident:
            counterexamples.append([a, b, c, d])
    result = dict(points=n, individual_acyclic_relations=len(dags),
                  quadruples_tested=tested,
                  quadruples_satisfying_original_conditions=premises,
                  of_these_satisfying_no_shortcut_condition=strong_premises,
                  counterexamples=counterexamples,
                  seconds=round(time.monotonic()-start, 4))
    if counterexamples:
        raise AssertionError(result)
    return result

records = [run(n) for n in range(4)]
report = dict(scope='exhaustive finite sanity check through three points only',
              all_passed=True, results=records)
out = Path(__file__).parent / 'exhaustive_original_conditions.json'
out.write_text(json.dumps(report, indent=2)+'\n')
print(json.dumps(report, indent=2))
