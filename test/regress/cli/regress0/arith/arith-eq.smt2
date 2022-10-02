; COMMAND-LINE:
; EXPECT: unsat
(set-logic QF_LRA)

(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun z () Real)

(assert (= z 0))
(assert (= (* 3 x) y))
(assert (= (+ 1 (* 5 x)) y))
(assert (= (+ 7 (* 4 x)) y))

(check-sat)
