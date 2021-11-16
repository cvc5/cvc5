; EXPECT: sat
(set-option :incremental false)
(set-logic ALL)


(declare-fun x () (Set (Tuple Int Int)))
(declare-fun y () (Set (Tuple Int Int)))
(declare-fun r () (Set (Tuple Int Int)))
(declare-fun z () (Tuple Int Int))
(assert (= z (tuple 1 2)))
(declare-fun zt () (Tuple Int Int))
(assert (= zt (tuple 2 1)))
(declare-fun v () (Tuple Int Int Int Int))
(assert (= v (tuple 1 2 2 1)))
(assert (set.member z x))
(assert (set.member zt y))
(assert (set.member v (rel.product x y)))
(check-sat)
