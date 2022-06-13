; EXPECT: sat
(set-option :incremental false)
(set-logic ALL)

(declare-fun x () (Relation Int Int))
(declare-fun y () (Relation Int Int))
(declare-fun z () (Relation Int Int))
(assert (set.member (tuple 1 3) x))
(assert (or (set.member (tuple 2 3) z) (set.member (tuple 2 1) z)))
(assert (= y (rel.transpose x)))
(assert (not (set.member (tuple 1 2) y)))
(assert (= x z))
(check-sat)
