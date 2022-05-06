(set-logic ALL)
(set-info :status unsat)
(assert (forall ((a Real)) (= (* (to_int (+ a 1.0)) (to_int a)) 1)))
(check-sat)
