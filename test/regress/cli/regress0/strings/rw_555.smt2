; EXPECT: unsat
(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () Int)
(assert (not (= (= "" (str.replace "A" x y)) (= "A" (str.replace "" y x)))))
(check-sat)
(exit)
