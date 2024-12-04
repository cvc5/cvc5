; REQUIRES: poly
; COMMAND-LINE: --theoryof-mode=term --nl-icp
; EXPECT: sat
(set-logic QF_NRA)
(declare-fun x () Real)
(declare-fun y () Real)
(assert (and (< 1 y) (= y (+ x (* x x)))))
(check-sat)
