; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(declare-fun x () (Bag Real))
(declare-fun y () (Bag Real))
(assert (not (= x y)))
(check-sat)
