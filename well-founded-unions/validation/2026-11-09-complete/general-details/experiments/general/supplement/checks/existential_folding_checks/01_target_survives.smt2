
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

; Original P1 at A-normal sources; both F shortcuts remain available.
(assert (forall ((x X) (y X) (v X))
  (=> (and (S x) (F x y) (B y v)) (or (Bp x v) (F x v)))))

(define-fun Rep ((v X) (u X)) Bool
  (and (S u) (forall ((x X)) (=> (and (S x) (E x v)) (E x u)))))
(assert (Rep z t))
(assert (S w))
(assert (B w z))
(define-fun Y ((x X)) Bool (and (S x) (B x z)))
(define-fun Sp ((x X)) Bool (and (S x) (not (B x z))))
(define-fun RepNew ((v X) (u X)) Bool
  (and (Sp u) (forall ((x X)) (=> (and (Sp x) (E x v)) (E x u)))))

(assert (not (Sp t)))
(check-sat)
