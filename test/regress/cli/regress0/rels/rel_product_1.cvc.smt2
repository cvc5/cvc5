; EXPECT: unsat
(set-option :incremental false)
(set-logic ALL)


(declare-fun x () (Relation Int Int Int))
(declare-fun y () (Relation Int Int Int))
(declare-fun r () (Relation Int Int Int))
(declare-fun z () (Tuple Int Int Int))
(assert (= z (tuple 1 2 3)))
(declare-fun zt () (Tuple Int Int Int))
(assert (= zt (tuple 3 2 1)))
(declare-fun v () (Tuple Int Int Int Int Int Int))
(assert (= v (tuple 1 2 3 3 2 1)))
(assert (set.member z x))
(assert (set.member zt y))
(assert (not (set.member v (rel.product x y))))
(check-sat)
