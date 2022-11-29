(set-logic ALL)
(set-info :status unsat)
(assert (forall ((a Real)) (exists ((b Int)) (= (exists ((c Int)) (<= a (to_real c) (+ a 1.0))) (and (>= (to_real b) (/ a (+ a 1.0))) (< 1.0 (+ a 1.0)))))))
(check-sat)
