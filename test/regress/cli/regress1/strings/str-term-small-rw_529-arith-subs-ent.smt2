; EXPECT: unsat
(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () Int)
(assert (not (= (str.replace x (str.at x 0) "") (str.substr x 1 (str.len x)))))
(check-sat)
(exit)
