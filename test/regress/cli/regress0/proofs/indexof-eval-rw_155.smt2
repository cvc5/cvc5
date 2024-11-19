; EXPECT: unsat
(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () Int)
(assert (not (= (str.substr x 0 (str.indexof x "" 1)) (str.at x 0))))
(check-sat)
(exit)
