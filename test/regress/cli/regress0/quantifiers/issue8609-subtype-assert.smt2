(set-logic ALL)
(set-info :status unsat)
(assert (forall ((r Int) (r9 Int)) (= 1.0 (/ (to_real r) (+ 0.5 (to_real r9))))))
(check-sat)
