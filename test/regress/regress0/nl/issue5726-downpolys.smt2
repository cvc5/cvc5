; COMMAND-LINE: --no-nl-ext --nl-cad
; REQUIRES: poly
; EXPECT: unsat
(set-logic QF_NRA)
(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun z () Real)
(assert (and (> x 0.0) (> 1.0 (+ 1.0 z)) (= y (+ y (* z x)))))
(check-sat)
