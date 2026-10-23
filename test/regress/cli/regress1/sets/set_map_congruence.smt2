; REQUIRES: unrestricted-mode
; EXPECT: unsat
; This is solved by congruence over set.map in the equality engine.
(set-logic HO_ALL)
(define-fun f ((x Int)) Int (+ x 1))
(declare-fun A () (Set Int))
(declare-fun B () (Set Int))
(declare-fun C () (Set Int))
(assert (or (= A B) (= A C)))
(assert (not (= (set.map f A) (set.map f B))))
(assert (not (= (set.map f A) (set.map f C))))
(check-sat)
