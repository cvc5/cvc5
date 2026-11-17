; REQUIRES: poly
; EXPECT: sat
(set-logic QF_NRA)
(set-info :status sat)
(declare-const x Real)
(declare-const y Real)
(declare-const z Real)
(assert (> (* (- z 1) (* (+ y 55) (- y 4))) 0))
(assert (< (* x x x x) 257))
(assert (> y 0))
(assert (> (* (- (* (- z 0) (- z 2)) 1) (* (+ y 55) (+ y x) y)) 0))
(assert (< (* (- z 2) (* (+ y 55) (- y 4) (+ y 3))) 0))
(check-sat)
