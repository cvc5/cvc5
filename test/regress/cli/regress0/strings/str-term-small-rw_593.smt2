; EXPECT: unsat
(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () Int)
(assert (not (= (str.replace x (str.replace "A" y x) "A") (str.replace x (str.replace y "A" x) y))))
(check-sat)
(exit)
