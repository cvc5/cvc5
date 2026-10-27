; EXPECT: unsat
(set-logic ALL)
(declare-fun x () String)
(declare-fun y () String)
(assert (str.contains (str.++ x "ABC" y) "DE"))
(assert (not (str.contains x "DE")))
(assert (not (str.contains y "DE")))
(check-sat)
