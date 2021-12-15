; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(declare-fun x () (Bag (_ BitVec 2)))
(declare-fun y () (Bag (_ BitVec 2)))
(assert (not (= x y)))
(check-sat)
