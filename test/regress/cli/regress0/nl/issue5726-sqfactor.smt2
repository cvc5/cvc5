; COMMAND-LINE: --nl-ext=none --nl-cov
; REQUIRES: poly
; EXPECT: sat
(set-logic QF_NRA)
(declare-fun x () Real)
(declare-fun y () Real)
(assert (and (> (* y y y y y y) 0) (> (- x (+ x (* x x (+ (* x x) (* y (- 1.0)))))) 0)))
(check-sat) 
