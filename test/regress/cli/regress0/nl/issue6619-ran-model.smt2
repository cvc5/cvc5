; REQUIRES: poly
; EXPECT: sat
(set-logic QF_NRA)
(declare-fun v () Bool)
(declare-fun r () Real)
(assert (> 1.0 (* r (- 1.0) (- 0.0 r 86.1))))
(assert (or v (= 1.0 (/ 1.0 (- r 86.1)))))
(check-sat)
