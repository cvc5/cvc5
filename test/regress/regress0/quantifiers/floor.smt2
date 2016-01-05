(set-logic LIRA)
(set-info :status unsat)
(assert (forall ((X Real)) (not (>= (+ (to_int (* 2 X)) (* (- 2) (to_int X))) 1)) ))
(check-sat)