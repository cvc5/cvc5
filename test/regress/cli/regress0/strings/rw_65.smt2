; EXPECT: unsat
(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () Int)
(assert (not (= (str.at x (str.indexof "B" "A" z)) "")))
(check-sat)
(exit)
