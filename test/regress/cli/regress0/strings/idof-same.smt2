; EXPECT: unsat
(set-logic ALL)
(declare-fun x () String)
(declare-fun y () String)
(assert (not (= (str.indexof (str.++ x y x) y 0) (str.indexof (str.++ x y) y 0))))
(check-sat)
