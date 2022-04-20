; REQUIRES: poly
; COMMAND-LINE: --nl-icp
; EXPECT: sat
(set-logic QF_NIA)
(declare-const a Int)
(assert (> (- a) (* (+ a a) (+ a 1))))
(check-sat)
