; EXPECT: unsat
(set-option :incremental false)
(set-logic ALL)


(declare-fun x () (Relation Int Int))
(declare-fun y () (Relation Int Int))
(declare-fun z () (Relation Int Int))
(declare-fun r () (Relation Int Int Int Int))
(assert (set.member (tuple 2 1) x))
(assert (set.member (tuple 2 3) x))
(assert (set.member (tuple 2 2) y))
(assert (set.member (tuple 4 7) y))
(assert (set.member (tuple 3 4) z))
(declare-fun v () (Tuple Int Int Int Int))
(assert (= v (tuple 4 3 2 1)))
(assert (= r (rel.product (rel.join (rel.transpose x) y) z)))
(assert (not (set.member v (rel.transpose r))))
(check-sat)
