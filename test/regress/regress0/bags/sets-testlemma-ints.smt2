; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(declare-fun x () (Bag Int))
(declare-fun y () (Bag Int))
(assert (not (= x y)))
(check-sat)
