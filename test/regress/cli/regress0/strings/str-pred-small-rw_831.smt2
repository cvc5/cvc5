; EXPECT: unsat
(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () Int)
(assert (not (= (not (str.contains x "A")) (= x (str.replace x "A" "B")))))
(check-sat)
(exit)
