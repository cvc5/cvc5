; REQUIRES: unrestricted-mode
; EXPECT: unsat
; This is solved by congruence over bag.filter in the equality engine.
(set-logic HO_ALL)
(define-fun P ((x Int)) Bool (> x 0))
(declare-fun A () (Bag Int))
(declare-fun B () (Bag Int))
(declare-fun C () (Bag Int))
(assert (or (= A B) (= A C)))
(assert (not (= (bag.filter P A) (bag.filter P B))))
(assert (not (= (bag.filter P A) (bag.filter P C))))
(check-sat)
