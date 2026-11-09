#!/usr/bin/env python3
"""Local folding obligations for existential incoming-edge representatives.

No projection function, identity-on-the-range law, choice principle, or
finiteness assumption is encoded. Each query uses only the representative
witnesses needed at that step. This is a supplementary SMT check, not a
formalization of the mathematical induction or the whole termination theorem.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import time

from z3_runner import run_z3

OUT = Path(__file__).resolve().parent / 'existential_folding_checks'
OUT.mkdir(exist_ok=True)

PREFIX = r'''
(set-option :timeout 15000)
(set-logic ALL)
(declare-sort X 0)
(declare-fun S (X) Bool)
(declare-fun B (X X) Bool)
(declare-fun Bp (X X) Bool)
(declare-fun F (X X) Bool)
(define-fun E ((x X) (y X)) Bool (or (B x y) (F x y)))
(declare-const z X)
(declare-const t X)
(declare-const w X)
(assert (forall ((x X)) (not (E x x))))
(assert (forall ((x X) (y X)) (=> (B x y) (Bp x y))))
(assert (forall ((x X) (y X))
  (=> (Bp x y)
      (or (B x y) (exists ((v X)) (and (B x v) (Bp v y)))))))
; No positive B-path from a B-successor of S ends at z.
(assert (forall ((x X) (v X))
  (=> (and (S x) (B x v)) (not (Bp v z)))))
'''
P1 = r'''
; Original P1 at A-normal sources; both F shortcuts remain available.
(assert (forall ((x X) (y X) (v X))
  (=> (and (S x) (F x y) (B y v)) (or (Bp x v) (F x v)))))
'''
WITNESSES = r'''
(define-fun Rep ((v X) (u X)) Bool
  (and (S u) (forall ((x X)) (=> (and (S x) (E x v)) (E x u)))))
(assert (Rep z t))
(assert (S w))
(assert (B w z))
(define-fun Y ((x X)) Bool (and (S x) (B x z)))
(define-fun Sp ((x X)) Bool (and (S x) (not (B x z))))
(define-fun RepNew ((v X) (u X)) Bool
  (and (Sp u) (forall ((x X)) (=> (and (Sp x) (E x v)) (E x u)))))
'''
BASE = PREFIX + P1 + WITNESSES
CASES = {
    '01_target_survives': '(assert (not (Sp t)))',
    '02_incoming_edge_transfer': r'''
(declare-const x X) (declare-const y X)
(assert (S x)) (assert (Y y)) (assert (E x y))
(assert (not (and (E x z) (E x t))))''',
    '03_retained_representative': r'''
(declare-const v X) (declare-const u X)
(assert (Rep v u)) (assert (not (B u z)))
(assert (not (RepNew v u)))''',
    '04_redirected_representative': r'''
(declare-const v X) (declare-const u X)
(assert (Rep v u)) (assert (B u z))
(assert (not (RepNew v t)))''',
    '05_witness_case_split': r'''
(declare-const v X) (declare-const u X)
(assert (Rep v u))
(assert (not (or (RepNew v u) (RepNew v t))))''',
}

CONSISTENCY = BASE.replace('(declare-sort X 0)',
    '(declare-datatypes () ((X U V W)))') + r'''
(assert (= w U)) (assert (= z V)) (assert (= t W))
(assert (forall ((x X)) (= (S x) (or (= x U) (= x W)))))
(assert (forall ((x X) (y X)) (= (B x y) (and (= x U) (= y V)))))
(assert (forall ((x X) (y X)) (= (Bp x y) (B x y))))
(assert (forall ((x X) (y X)) (= (F x y) (and (= x U) (= y W)))))
'''
# A four-point graph falsifies transfer when the middle rerouting hypothesis
# is removed. This validates that this test can detect that missing premise.
NEGATIVE = (PREFIX + WITNESSES).replace('(declare-sort X 0)',
    '(declare-datatypes () ((X U V W T)))') + r'''
(assert (= w V)) (assert (= z W)) (assert (= t T))
(assert (forall ((x X)) (= (S x) (or (= x U) (= x V) (= x T)))))
(assert (forall ((x X) (y X)) (= (B x y) (and (= x V) (= y W)))))
(assert (forall ((x X) (y X)) (= (Bp x y) (B x y))))
(assert (forall ((x X) (y X)) (= (F x y)
  (or (and (= x U) (= y V)) (and (= x V) (= y T))))))
(assert (and (S U) (Y V) (E U V) (not (E U t))))
'''


def main() -> None:
    solver = run_z3('(get-info :version)\n').strip()
    records = []
    queries = [('00_consistent_witnesses', CONSISTENCY, 'sat')]
    queries += [(name, BASE + '\n' + negated, 'unsat')
                for name, negated in CASES.items()]
    queries += [('06_missing_P1_negative_control', NEGATIVE, 'sat')]
    for name, body, expected in queries:
        smt = body + '\n(check-sat)\n'
        (OUT / (name + '.smt2')).write_text(smt)
        started = time.monotonic()
        status = run_z3(smt).strip()
        (OUT / (name + '.out')).write_text(status + '\n')
        record = {'name': name, 'expected': expected, 'status': status,
                  'seconds': round(time.monotonic() - started, 5),
                  'solver': solver,
                  'smt_sha256': hashlib.sha256(smt.encode()).hexdigest()}
        records.append(record)
        print(json.dumps(record), flush=True)
        (OUT / 'results.json').write_text(json.dumps(records, indent=2) + '\n')
        if status != expected:
            raise RuntimeError(f'{name}: expected {expected}, got {status!r}')


if __name__ == '__main__':
    main()
