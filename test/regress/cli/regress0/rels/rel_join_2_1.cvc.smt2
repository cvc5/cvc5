; EXPECT: sat
(set-option :incremental false)
(set-logic ALL)


(declare-fun x () (Relation Int Int))
(declare-fun y () (Relation Int Int Int))
(declare-fun z () (Tuple Int Int))
(assert (= z (tuple 1 2)))
(declare-fun zt () (Tuple Int Int Int))
(assert (= zt (tuple 2 1 3)))
(declare-fun a () (Tuple Int Int Int))
(assert (= a (tuple 1 1 3)))
(assert (set.member z x))
(assert (set.member zt y))
(assert (set.member a (rel.join x y)))
(check-sat)
