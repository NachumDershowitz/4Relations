
(set-option :timeout 15000)
(set-logic ALL)
(declare-sort O 0)
(declare-fun lt (O O) Bool)
(define-fun le ((a O) (b O)) Bool (or (= a b) (lt a b)))
(declare-const alpha O) (declare-const beta O) (declare-const gamma O)
(assert (forall ((a O)) (not (lt a a))))
(assert (forall ((a O) (b O) (c O)) (=> (and (lt a b) (lt b c)) (lt a c))))
(assert (forall ((a O)) (= (lt a alpha) (le a beta))))

 (assert (not (lt beta alpha)))
(check-sat)
