; REQUIRES: poly
; EXPECT: sat
(set-logic QF_UFNRA)
(declare-fun w (Real) Real)
(declare-fun m (Real) Real)
(declare-fun t (Real) Bool)
(declare-fun u (Real) Real)
(assert (= (m 1) (w 0)))
(assert (not (t 0.0)))
(assert (= (+ 1 (w 1)) (* (u 1.0) (m (+ 1 (w 1))))))
(assert (= (t 0) (= (w 1) (* (u 1) (u 0)))))
(check-sat)
