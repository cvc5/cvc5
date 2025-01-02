; REQUIRES: poly
; EXPECT: sat
(set-logic QF_NRA)
(set-info :status sat)
(declare-fun x () Real)
(assert (= (* x x) 2))
(assert (> x 0))
(assert (> (+ (* x x) (* (- 2.8) x)) (- 1.9598)))
(assert (> (+ (* x x) (* (- 2.8284271247) x)) (- 1.9999999999999)))
(assert (> (+ (* x x) (* (- 2.82842712475) x)) (- 2.00000001)))
(check-sat)
