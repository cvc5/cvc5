; EXPECT: unsat
(set-logic ALL)
(declare-fun f (Int) Int)
(define-fun P ((x Int)) Bool (forall ((x Int)) (> (f x) 0)))
(assert (P 0))
(assert (= (f 0) 0))
(check-sat)
