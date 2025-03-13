; EXPECT: unsat
(set-logic ALL)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () String)
(declare-fun w () String)
(assert (not (str.contains (str.++ x y z "AB" w) (str.++ y z "A"))))
(check-sat)
