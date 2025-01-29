; EXPECT: unsat
(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () Int)
(assert (not (= (str.suffixof "B" (str.replace "B" "A" x)) true)))
(check-sat)
(exit)
