(set-logic LIA)
(set-info :status unsat)
(assert (forall ((U Int) (V Int)) (not (= (* 3 U) (+ 22 (* (- 5) V)))) ) )
(check-sat)
