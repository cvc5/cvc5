; EXPECT: unsat
(set-logic ALL)
(declare-fun x () String)
(declare-fun y () String)
(assert (distinct (str.replace "" x (str.++ "B" y)) (str.replace (str.replace "" x y) x "B")))
(check-sat)
