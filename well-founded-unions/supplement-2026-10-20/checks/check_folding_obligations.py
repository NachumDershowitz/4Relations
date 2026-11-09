"""Check domain-independent, first-order obligations for the new folding step.

These SMT checks supplement, but do not replace, the mathematical induction
and termination proofs in the manuscript. Bp denotes B transitive closure;
only the two closure properties needed here are axiomatized.
"""
from pathlib import Path
import json, time
from z3_runner import run_z3

OUT=Path(__file__).parent/'folding_checks'
OUT.mkdir(exist_ok=True)
BASE=r'''
(set-option :timeout 15000)
(set-logic ALL)
(declare-sort X 0)
(declare-fun S (X) Bool)
(declare-fun B (X X) Bool)
(declare-fun Bp (X X) Bool)
(declare-fun F (X X) Bool)
(define-fun E ((x X) (y X)) Bool (or (B x y) (F x y)))
(declare-fun p (X) X)
(declare-const z X)
(declare-const y0 X)
(assert (S y0))
(assert (B y0 z))
(assert (forall ((x X)) (not (E x x))))
(assert (forall ((x X) (y X)) (=> (B x y) (Bp x y))))
(assert (forall ((x X) (y X))
  (=> (Bp x y) (or (B x y) (exists ((v X)) (and (B x v) (Bp v y)))))))
; z has no B+-predecessor among the B-successors of S.
(assert (forall ((x X) (v X)) (=> (and (S x) (B x v)) (not (Bp v z)))))
; The original P1 on A-minimal sources, with all F shortcuts allowed.
(assert (forall ((x X) (y X) (v X))
  (=> (and (S x) (F x y) (B y v)) (or (Bp x v) (F x v)))))
; Projection range, identity on S, and incoming-edge invariant.
(assert (forall ((v X)) (S (p v))))
(assert (forall ((v X)) (=> (S v) (= (p v) v))))
(assert (forall ((x X) (v X)) (=> (and (S x) (E x v)) (E x (p v)))))
(define-fun Y ((x X)) Bool (and (S x) (B x z)))
(define-fun Sp ((x X)) Bool (and (S x) (not (Y x))))
(define-fun pp ((v X)) X (ite (Y (p v)) (p z) (p v)))
'''
CASES={
 '01_surviving_target': '(assert (not (Sp (p z))))',
 '02_transfer': '''(declare-const x X) (declare-const y X)
 (assert (S x)) (assert (Y y)) (assert (E x y)) (assert (not (E x z)))''',
 '03_new_range': '''(declare-const v X) (assert (not (Sp (pp v))))''',
 '04_new_identity': '''(declare-const x X) (assert (Sp x)) (assert (not (= (pp x) x)))''',
 '05_new_projection': '''(declare-const x X) (declare-const v X)
 (assert (Sp x)) (assert (E x v)) (assert (not (E x (pp v))))''',
 '06_strict_image_decrease': '''(declare-const x X) (assert (Sp x)) (assert (B x z))''',
}
records=[]
version_info=run_z3('(get-info :version)\n').strip()
base_model = BASE.replace('(declare-sort X 0)', '(declare-datatypes () ((X U V W)))') + r'''

(assert (= y0 U)) (assert (= z V))
(assert (forall ((x X)) (= (S x) (or (= x U) (= x W)))))
(assert (forall ((x X) (y X)) (= (B x y) (and (= x U) (= y V)))))
(assert (forall ((x X) (y X)) (= (Bp x y) (B x y))))
(assert (forall ((x X) (y X)) (= (F x y) (and (= x U) (= y W)))))
(assert (= (p U) U)) (assert (= (p V) W)) (assert (= (p W) W))
(check-sat)
'''
(OUT/'00_base_consistency.smt2').write_text(base_model)
base_result=run_z3(base_model).strip()
(OUT/'00_base_consistency.out').write_text(base_result+'\n')
print('Base assumptions with an explicit three-point model:',base_result,flush=True)
assert base_result=='sat', 'The non-vacuity check did not close.'
for name,neg in CASES.items():
    smt=BASE+'\n'+neg+'\n(check-sat)\n'
    (OUT/(name+'.smt2')).write_text(smt)
    t=time.monotonic();result=run_z3(smt).strip();elapsed=time.monotonic()-t
    row={'obligation':name,'status':result,'seconds':round(elapsed,4),'solver':version_info}
    print(json.dumps(row),flush=True);records.append(row)
    (OUT/(name+'.out')).write_text(result+'\n')
(OUT/'results.json').write_text(json.dumps(records,indent=2)+'\n')
assert all(r['status']=='unsat' for r in records), 'An obligation did not close.'
