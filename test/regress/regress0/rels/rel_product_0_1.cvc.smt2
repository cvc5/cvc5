; EXPECT: sat
(set-option :incremental false)
(set-logic ALL)


(declare-fun x () (Set (Tuple Int Int)))
(declare-fun y () (Set (Tuple Int Int)))
(declare-fun r () (Set (Tuple Int Int)))
(declare-fun z () (Tuple Int Int))
(assert (= z (mkTuple 1 2)))
(declare-fun zt () (Tuple Int Int))
(assert (= zt (mkTuple 2 1)))
(declare-fun v () (Tuple Int Int Int Int))
(assert (= v (mkTuple 1 2 2 1)))
(assert (member z x))
(assert (member zt y))
(assert (member v (product x y)))
(check-sat)
