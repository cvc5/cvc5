; COMMAND-LINE: --no-check-unsat-cores --no-check-proofs
; EXPECT: unsat
(set-logic QF_LRA)
(set-info :smt-lib-version 2.0)

(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun z () Real)

; Both strict and non-strict inequalities.
(assert (< y 0))
(assert (>= y x))
(assert (>= y (- x)))

(check-sat)
