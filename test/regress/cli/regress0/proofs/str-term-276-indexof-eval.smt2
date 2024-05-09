; EXPECT: unsat
(set-info :smt-lib-version 2.6)
(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () Int)
(assert (not (= (str.substr x (str.indexof "B" x 1) z) "")))
(check-sat)
(exit)
