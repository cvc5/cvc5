; EXPECT: sat
(set-option :incremental false)
(set-logic ALL)


(declare-fun x () (Set (Tuple Int Int Int)))
(declare-fun y () (Set (Tuple Int Int Int)))
(declare-fun r () (Set (Tuple Int Int Int Int Int Int)))
(declare-fun z () (Tuple Int Int Int))
(assert (= z (tuple 1 2 3)))
(declare-fun zt () (Tuple Int Int Int))
(assert (= zt (tuple 3 2 1)))
(assert (member z x))
(assert (member zt y))
(assert (member (tuple 1 1 1 1 1 1) r))
(assert (= r (product x y)))
(check-sat)
