; EXPECT: unsat
(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () Int)
(assert (not (= (str.prefixof (str.substr x 1 0) y) true)))
(check-sat)
(exit)
