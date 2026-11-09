"""Local checks for the height extensions. NOT a complete theorem prover.

Each item is a universally valid first-order proof obligation. Integer heights
are used only where the manuscript uses finite heights. A separate abstract
order obligation tests the successor-rank argument. The induction and
well-foundedness arguments remain in the Rocq source, not in these checks.
"""
from pathlib import Path
import json
import time
from z3_runner import run_z3

OUT = Path(__file__).parent / 'height_checks'
OUT.mkdir(exist_ok=True)
BASE = r'''
(set-option :timeout 15000)
(set-logic ALL)
(declare-sort X 0)
(declare-fun S (X) Bool)
(declare-fun B (X X) Bool)
(declare-fun Bp (X X) Bool)
(declare-fun F (X X) Bool)
(define-fun E ((x X) (y X)) Bool (or (B x y) (F x y)))
(declare-fun h (X) Int)
(declare-fun p (X) X)
(declare-const H Int)
(assert (> H 0))
(assert (forall ((x X)) (>= (h x) 0)))
(assert (forall ((x X)) (=> (S x) (<= (h x) H))))
(assert (forall ((x X) (y X)) (=> (B x y) (< (h y) (h x)))))
(assert (forall ((x X) (y X)) (=> (Bp x y) (< (h y) (h x)))))
(assert (forall ((x X) (z X))
  (=> (Bp x z) (or (B x z) (exists ((u X)) (and (B x u) (Bp u z)))))))
(assert (forall ((x X) (y X) (z X))
  (=> (and (S x) (F x y) (B y z)) (or (Bp x z) (F x z)))))
(assert (forall ((z X)) (S (p z))))
(assert (forall ((x X) (z X)) (=> (and (S x) (E x z)) (E x (p z)))))
(define-fun Dom ((u X) (v X)) Bool
  (and (S u) (S v) (E u v)
    (forall ((x X)) (=> (and (S x) (E x u)) (E x v)))))
(define-fun Top ((x X)) Bool (and (S x) (= (h x) H)))
(define-fun Lower ((x X)) Bool (and (S x) (< (h x) H)))
'''
CASES = {
 '01_incoming_top_edge_is_F': r'''
 (declare-const x X) (declare-const y X)
 (assert (S x)) (assert (Top y)) (assert (E x y)) (assert (not (F x y)))''',
 '02_two_step_path_to_top_successor_impossible': r'''
 (declare-const x X) (declare-const u X) (declare-const z X)
 (assert (S x)) (assert (= (h z) (- H 1)))
 (assert (B x u)) (assert (Bp u z))''',
 '03_top_transfer': r'''
 (declare-const x X) (declare-const y X) (declare-const z X)
 (assert (S x)) (assert (Top y)) (assert (E x y))
 (assert (B y z)) (assert (= (h z) (- H 1))) (assert (not (E x z)))''',
 '04_top_has_dominating_representative': r'''
 (declare-const y X) (declare-const z X)
 (assert (Top y)) (assert (B y z)) (assert (= (h z) (- H 1)))
 (assert (not (Dom y (p z))))''',
 '05_domination_is_transitive': r'''
 (declare-const x X) (declare-const y X) (declare-const z X)
 (assert (Dom x y)) (assert (Dom y z)) (assert (not (Dom x z)))''',
 '06_top_domination_is_in_F': r'''
 (declare-const x X) (declare-const y X)
 (assert (Top x)) (assert (Top y)) (assert (Dom x y)) (assert (not (F x y)))''',
 '07_lower_has_smaller_uniform_bound': r'''
 (declare-const x X) (assert (Lower x)) (assert (> (h x) (- H 1)))''',
 '08_composed_representatives_preserve_edges': r'''
 (declare-fun r (X) X)
 (assert (forall ((x X)) (=> (S x) (Lower (r x)))))
 (assert (forall ((x X) (u X))
   (=> (and (S x) (S u) (E x u)) (E x (r u)))))
 (declare-const x X) (declare-const z X)
 (assert (Lower x)) (assert (E x z)) (assert (not (E x (r (p z)))))''',
 '09_composed_representatives_have_lower_range': r'''
 (declare-fun r (X) X)
 (assert (forall ((x X)) (=> (S x) (Lower (r x)))))
 (declare-const z X) (assert (not (Lower (r (p z)))))''',
}
# Non-vacuity: an explicit model with a top point and its maximal-height
# successor satisfies the whole local context and the representative invariant.
MODEL = BASE.replace('(declare-sort X 0)', '(declare-datatypes () ((X U V W)))') + r'''
(assert (= H 1))
(assert (= (h U) 1)) (assert (= (h V) 0)) (assert (= (h W) 0))
(assert (forall ((x X)) (= (S x) (or (= x U) (= x W)))))
(assert (forall ((x X) (y X)) (= (B x y) (and (= x U) (= y V)))))
(assert (forall ((x X) (y X)) (= (Bp x y) (B x y))))
(assert (forall ((x X) (y X)) (= (F x y) (and (= x U) (= y W)))))
(assert (= (p U) U)) (assert (= (p V) W)) (assert (= (p W) W))
'''
STRONG = r'''
(set-option :timeout 15000)
(set-logic ALL)
(declare-sort X 0)
(declare-fun B (X X) Bool)
(declare-fun Bp (X X) Bool)
(declare-fun F (X X) Bool)
(declare-fun M (X) Bool)
(declare-fun h (X) Int)
(assert (forall ((x X)) (>= (h x) 0)))
(assert (forall ((x X) (y X)) (=> (Bp x y) (< (h y) (h x)))))
(assert (forall ((x X) (y X) (z X))
  (=> (and (M x) (F x y) (B y z)) (Bp x z))))
(assert (forall ((y X)) (=> (> (h y) 0)
  (exists ((z X)) (and (B y z) (= (h z) (- (h y) 1)))))))
'''
NORMAL = r'''
(set-option :timeout 15000)
(set-logic ALL)
(declare-sort X 0)
(declare-fun M (X) Bool)
(declare-fun E (X X) Bool)
(declare-fun p (X) X)
(declare-fun h (X) Int)
(declare-const H Int)
(declare-const seed X)
(assert (M seed)) (assert (<= (h seed) H))
(define-fun S ((x X)) Bool (and (M x) (<= (h x) H)))
(assert (forall ((x X) (y X))
  (=> (and (M x) (M y) (E x y)) (<= (h y) (h x)))))
(assert (forall ((z X)) (M (p z))))
(assert (forall ((x X) (z X)) (=> (and (M x) (E x z)) (E x (p z)))))
'''
RANK = r'''
(set-option :timeout 15000)
(set-logic ALL)
(declare-sort O 0)
(declare-fun lt (O O) Bool)
(define-fun le ((a O) (b O)) Bool (or (= a b) (lt a b)))
(declare-const alpha O) (declare-const beta O) (declare-const gamma O)
(assert (forall ((a O)) (not (lt a a))))
(assert (forall ((a O) (b O) (c O)) (=> (and (lt a b) (lt b c)) (lt a c))))
(assert (forall ((a O)) (= (lt a alpha) (le a beta))))
'''
EXTRA = {
 '10_strong_F_does_not_increase_finite_height': (STRONG, r'''
 (declare-const x X) (declare-const y X)
 (assert (M x)) (assert (F x y)) (assert (> (h y) (h x)))'''),
 '11_incoming_bounded_subset_forces_bounded_representative': (NORMAL, r'''
 (declare-const x X) (declare-const z X)
 (assert (S x)) (assert (E x z)) (assert (not (S (p z))))'''),
 '12_no_incoming_edge_allows_arbitrary_bounded_seed': (NORMAL, r'''
 (declare-const z X)
 (assert (forall ((x X)) (=> (S x) (not (E x z)))))
 (assert (not (and (S seed) (forall ((x X)) (=> (and (S x) (E x z)) (E x seed))))))'''),
 '13_successor_rank_has_no_intermediate_value': (RANK, r'''
 (assert (lt beta gamma)) (assert (lt gamma alpha))'''),
 '14_successor_rank_is_strictly_above_predecessor': (RANK, r'''
 (assert (not (lt beta alpha)))'''),
}

def check(name: str, script: str, expected: str) -> dict:
    text = script + '\n(check-sat)\n'
    (OUT / f'{name}.smt2').write_text(text)
    started = time.monotonic()
    result = run_z3(text).strip()
    (OUT / f'{name}.out').write_text(result + '\n')
    row = dict(obligation=name, status=result, expected=expected,
               seconds=round(time.monotonic()-started, 4))
    print(json.dumps(row), flush=True)
    if result != expected:
        raise RuntimeError(f'{name}: expected {expected}, received {result}')
    return row

records = [check('00_base_consistency', MODEL, 'sat')]
for name, negated in CASES.items():
    records.append(check(name, BASE + negated, 'unsat'))
for name, (base, negated) in EXTRA.items():
    records.append(check(name, base + negated, 'unsat'))
# Separate consistency checks avoid deriving conclusions from inconsistent
# strong-propagation or abstract-order premises.
records.append(check('15_strong_context_consistency', STRONG, 'sat'))
records.append(check('16_rank_context_consistency', RANK, 'sat'))
# Negative control: after omitting the P1 rerouting constraint, top-edge
# transfer must no longer be derivable. A fixed model exhibits that failure.
NEG = r'''
(set-logic ALL)
(declare-datatypes () ((X U V W)))
(define-fun B ((x X) (y X)) Bool (and (= x V) (= y W)))
(define-fun F ((x X) (y X)) Bool (and (= x U) (= y V)))
(define-fun E ((x X) (y X)) Bool (or (B x y) (F x y)))
(assert (E U V)) (assert (B V W)) (assert (not (E U W)))
'''
records.append(check('17_negative_control_without_rerouting', NEG, 'sat'))
report = dict(scope='local first-order obligations only; not kernel verification',
              kernel_verified=False, solver=run_z3('(get-info :version)').strip(),
              results=records)
(OUT / 'results.json').write_text(json.dumps(report, indent=2)+'\n')
