
(set-logic ALL)
(declare-datatypes () ((X U V W)))
(define-fun B ((x X) (y X)) Bool (and (= x V) (= y W)))
(define-fun F ((x X) (y X)) Bool (and (= x U) (= y V)))
(define-fun E ((x X) (y X)) Bool (or (B x y) (F x y)))
(assert (E U V)) (assert (B V W)) (assert (not (E U W)))

(check-sat)
