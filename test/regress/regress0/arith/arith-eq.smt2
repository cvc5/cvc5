; COMMAND-LINE: --no-check-unsat-cores --no-check-proofs
; EXPECT: unsat
(set-logic QF_LRA)
(set-info :smt-lib-version 2.0)

(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun z () Real)

(assert (= z 0))
(assert (= (* 3 x) y))
(assert (= (+ 1 (* 5 x)) y))
(assert (= (+ 7 (* 4 x)) y))

(check-sat)
