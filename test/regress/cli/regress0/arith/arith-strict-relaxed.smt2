; COMMAND-LINE:
; EXPECT: unsat
(set-logic QF_LRA)

(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun z () Real)

; Both strict and non-strict inequalities.
(assert (< y 0))
(assert (>= y x))
(assert (>= y (- x)))

(check-sat)
