#!/usr/bin/env python3
"""Exhaustive three-point check of the representative-elimination lemma.

No assertions are used: every failed invariant raises RuntimeError, including
when run with Python optimization. This is a finite test, not a proof of the
unrestricted lemma.
"""
import json


def main() -> None:
    n = 3
    full = (1 << (n * n)) - 1
    points = range(n)
    diag = sum(1 << (n * x + x) for x in points)

    def edge(p: int, x: int, y: int) -> bool:
        return bool(p & (1 << (n * x + y)))

    def plus(p: int) -> int:
        for k in points:
            for x in points:
                for y in points:
                    if edge(p, x, k) and edge(p, k, y):
                        p |= 1 << (n * x + y)
        return p

    def members(s: int) -> list[int]:
        return [x for x in points if s & (1 << x)]

    def representatives(k: int, s: int, z: int) -> list[int]:
        return [t for t in members(s)
                if all(not edge(k, x, z) or edge(k, x, t)
                       for x in members(s))]

    def rep(k: int, s: int) -> bool:
        return bool(s) and all(representatives(k, s, z) for z in points)

    def targets(q: int, s: int) -> int:
        return sum(1 << z for z in points
                   if any(edge(q, y, z) for y in members(s)))

    def require(cond: bool, message: str) -> None:
        if not cond:
            raise RuntimeError(message)

    closures = [plus(q) for q in range(full + 1)]
    dag = [q for q in range(full + 1) if not closures[q] & diag]
    examined = applicable = targets_tested = witnesses_tested = 0
    for k in range(full + 1):
        if k & diag:
            continue
        for q in dag:
            if q & ~k:
                continue
            qp = closures[q]
            for s in range(1, 1 << n):
                examined += 1
                v = targets(q, s)
                if not v or not rep(k, s):
                    continue
                local = all(not (edge(k & ~q, x, y) and edge(q, y, z))
                            or edge(qp | k, x, z)
                            for x in members(s) for y in members(s)
                            for z in points)
                if not local:
                    continue
                applicable += 1
                eligible = [z for z in members(v)
                            if not any(edge(qp, w, z) for w in members(v))]
                require(bool(eligible), 'No eligible target in a finite acyclic image')
                for z in eligible:
                    targets_tested += 1
                    yset = sum(1 << y for y in members(s) if edge(q, y, z))
                    sp = s & ~yset
                    vp = targets(q, sp)
                    require(bool(yset), 'Empty set to delete')
                    require(bool(sp) and sp != s, 'Deletion is not nonempty and proper')
                    require(rep(k, sp), 'Representative property lost')
                    require(vp != v and not vp & ~v and not vp & (1 << z),
                            'Image did not decrease as specified')
                    for t in representatives(k, s, z):
                        witnesses_tested += 1
                        require(bool(sp & (1 << t)), 'Target representative deleted')
                        require(all(not edge(k, x, y) or edge(k, x, t)
                                    for x in members(s) for y in members(yset)),
                                'Incoming-edge transfer failed')
    require(applicable > 0 and witnesses_tested > 0, 'Vacuous test')
    print(json.dumps({'domain_size': n,
                      'admissible_relation_subset_triples': examined,
                      'triples_satisfying_lemma_premises': applicable,
                      'eligible_targets_tested': targets_tested,
                      'representative_witnesses_tested': witnesses_tested,
                      'failures': 0}, sort_keys=True))


if __name__ == '__main__':
    main()
