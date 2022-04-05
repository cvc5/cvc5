(set-logic ALL)
(set-info :status unsat)
(assert (forall ((a Real)) (exists ((b Int)) (= (exists ((c Int)) (<= a c (+ a 1))) (and (>= b (/ a (+ a 1))) (< 1 (+ a 1)))))))
(check-sat)
