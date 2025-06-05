; EXPECT: unsat
(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () Int)
(assert (not (= (= "" (str.replace x y x)) (= x ""))))
(check-sat)
(exit)
