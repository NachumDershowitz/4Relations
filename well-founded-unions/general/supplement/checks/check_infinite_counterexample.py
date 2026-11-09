#!/usr/bin/env python3
"""Symbolic checks of the entire infinite counterexample, not a finite sample.

The domain is {-2,-1,0,1,...}; p=-2 and q=-1. Each negative query has free
integer variables, so UNSAT checks all indices at once. Reroutings use
explicit witnesses. Ranking into N or lexicographically ordered N x N
establishes individual termination by the usual well-founded ranking lemma.
The solver checks the edge-wise decreases; it does not formalize that lemma.
Z3 proof traces are retained, but are not independently kernel checked.
"""
from __future__ import annotations
import hashlib
import json
from pathlib import Path
import time
from z3_runner import run_z3

OUT = Path(__file__).parent / 'infinite_checks'
OUT.mkdir(exist_ok=True)
BASE = r'''
(set-option :timeout 15000)
(set-logic ALL)
(define-fun valid ((x Int)) Bool (>= x (- 2)))
(define-fun A ((x Int) (y Int)) Bool
  (and (>= x 0)
    (or (and (= (mod x 2) 0) (= y (- 1)))
        (and (= (mod x 2) 1) (= y (- 2))))))
(define-fun B ((x Int) (y Int)) Bool
  (or (and (= x (- 2)) (>= y 0) (= (mod y 2) 0))
      (and (= x (- 1)) (>= y 0) (= (mod y 2) 1))
      (and (>= x 1) (= y (- x 1)))))
(define-fun C ((x Int) (y Int)) Bool
  (and (= x (- 1)) (= y (- 2))))
(define-fun D ((x Int) (y Int)) Bool
  (or (and (= x (- 2)) (= y (- 1)))
      (and (= x 0) (= y (- 2)))))
(define-fun F ((x Int) (y Int)) Bool (or (C x y) (D x y)))
(define-fun E ((x Int) (y Int)) Bool (or (B x y) (F x y)))
(define-fun R ((x Int) (y Int)) Bool (or (A x y) (E x y)))
(define-fun aw ((x Int)) Int (ite (= (mod x 2) 0) (- 1) (- 2)))
(define-fun ra ((x Int)) Int (ite (>= x 0) 1 0))
(define-fun rb1 ((x Int)) Int (ite (or (= x (- 2)) (= x (- 1))) 1 0))
(define-fun rb2 ((x Int)) Int (ite (>= x 0) x 0))
(define-fun rc ((x Int)) Int (ite (= x (- 1)) 1 0))
(define-fun rd ((x Int)) Int (ite (= x 0) 2 (ite (= x (- 2)) 1 0)))
(declare-const x Int)
(declare-const y Int)
(declare-const z Int)
'''
CASES = {
 '01_endpoint_domain': ('(R x y)', '(and (valid x) (valid y))'),
 '02_nonnegative_ranks': ('(valid x)', '(and (>= (ra x) 0) (>= (rb1 x) 0) (>= (rb2 x) 0) (>= (rc x) 0) (>= (rd x) 0))'),
 '03_A_rank_decrease': ('(A x y)', '(< (ra y) (ra x))'),
 '04_B_lex_rank_decrease': ('(B x y)', '(or (< (rb1 y) (rb1 x)) (and (= (rb1 y) (rb1 x)) (< (rb2 y) (rb2 x))))'),
 '05_C_rank_decrease': ('(C x y)', '(< (rc y) (rc x))'),
 '06_D_rank_decrease': ('(D x y)', '(< (rd y) (rd x))'),
 '07_P0_stronger_explicit_witness': ('(and (E x y) (A y z))', '(or (F x z) (and (A x (aw x)) (F (aw x) z)))'),
 '08_P1_stronger_explicit_witness': ('(and (F x y) (B y z))', '(or (and (B x (+ z 1)) (B (+ z 1) z)) (and (A x (- 1)) (B (- 1) (+ z 1)) (B (+ z 1) z)))'),
 '09_Q2_stronger_explicit_witness': ('(and (D x y) (C y z))', '(and (B x 0) (D 0 z))'),
 '10_two_cycle': ('true', '(and (D (- 2) (- 1)) (C (- 1) (- 2)))'),
 '11_cycle_even_steps': ('(>= x 0)', '(R (ite (= (mod x 2) 0) (- 2) (- 1)) (ite (= (mod (+ x 1) 2) 0) (- 2) (- 1)))'),
}
records = []
version = run_z3('(get-info :version)\n').strip()
for name, (premise, conclusion) in CASES.items():
    smt = BASE + f'\n(assert {premise})\n(assert (not {conclusion}))\n(check-sat)\n(get-proof)\n'
    smt = '(set-option :produce-proofs true)\n' + smt
    (OUT / (name + '.smt2')).write_text(smt)
    started = time.monotonic()
    result = run_z3(smt, proofs=True)
    (OUT / (name + '.out')).write_text(result)
    status = result.splitlines()[0].strip()
    row = dict(obligation=name, status=status, expected='unsat', seconds=round(time.monotonic()-started, 4),
               input_sha256=hashlib.sha256(smt.encode()).hexdigest())
    print(json.dumps(row), flush=True)
    records.append(row)
    if status != 'unsat' or '(proof' not in result or '(error' in result:
        raise RuntimeError(f'{name}: did not obtain an UNSAT proof trace')

# A model of the definitions and real edges, excluding vacuous all-empty relations.
positive = BASE + r'''
(assert (and (A 0 (- 1)) (A 1 (- 2)) (B (- 2) 0) (B (- 1) 1)
             (B 1 0) (C (- 1) (- 2)) (D (- 2) (- 1)) (D 0 (- 2))))
(check-sat)
'''
# A deliberately too-short B rerouting fails: 0 D p B 0 cannot reroute by B alone.
negative = BASE + r'''
(assert (and (F 0 (- 2)) (B (- 2) 0) (not (B 0 0))))
(check-sat)
'''
for name, smt in [('12_nonvacuity', positive), ('13_negative_control', negative)]:
    (OUT / (name + '.smt2')).write_text(smt)
    output = run_z3(smt)
    (OUT / (name + '.out')).write_text(output)
    status = output.strip()
    if status != 'sat':
        raise RuntimeError(f'{name}: expected sat, got {status}')
    row = dict(obligation=name, status=status, expected='sat')
    records.append(row)
    print(json.dumps(row), flush=True)
report = dict(all_passed=True, solver=version,
    scope='Symbolic all-integer-index checks of exact edge definitions, explicit reroutings, rankings and infinite alternating chain',
    proof_traces_retained=True, independently_kernel_checked=False,
    standard_mathematical_bridge='Lexicographic N x N and N are well-founded; an edge-decreasing ranking implies termination.',
    results=records)
(OUT / 'results.json').write_text(json.dumps(report, indent=2) + '\n')
