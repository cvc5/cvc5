(declare-fun a () Int)
(assert (distinct 0 (/ a (+ 0.5 a))))
(check-sat)
