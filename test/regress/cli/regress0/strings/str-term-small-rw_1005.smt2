; EXPECT: unsat
(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () Int)
(assert (not (= (str.replace (str.replace "B" x y) "A" y) (str.replace "B" x (str.replace y "A" y)))))
(check-sat)
(exit)
