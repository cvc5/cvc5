; REQUIRES: poly
; COMMAND-LINE: --nl-ext-tplanes
; EXPECT: unsat
(set-logic QF_NRA)
(set-info :status unsat)
(declare-fun x () Real)
(assert (= (* x x) 2))
(assert (> x 0))
(assert (or 
(> (+ (* x x) (* (- 2.8) x)) (- 1.95))
(> (+ (* x x) (* (- 2.8284271247) x)) (- 1.999999))
(> (+ (* x x) (* (- 2.82842712475) x)) (- 2.0000000000000000000000000001))
))
(check-sat)
