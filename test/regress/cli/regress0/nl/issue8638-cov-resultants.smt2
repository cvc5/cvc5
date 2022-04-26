; REQUIRES: poly
; EXPECT: sat
(set-logic QF_NRA)
(declare-fun y () Real)
(declare-fun p () Real)
(declare-fun c () Real)
(assert (< 1 c))
(assert (< 0.0 (/ (+ y p 1.0) c)))
(assert (and (> (* y y y y) 0) (> (* y y y p) 0)))
(check-sat)