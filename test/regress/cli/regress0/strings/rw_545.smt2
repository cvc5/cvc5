; EXPECT: unsat
(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () Int)
(assert (not (= (str.replace x (str.replace x "A" "B") "A") (str.replace x (str.replace x "A" x) "A"))))
(check-sat)
(exit)
