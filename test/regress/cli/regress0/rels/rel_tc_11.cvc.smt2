; EXPECT: unsat
(set-option :incremental false)
(set-logic ALL)


(declare-fun x () (Relation Int Int))
(declare-fun y () (Relation Int Int))
(declare-fun z () (Relation Int Int Int Int))
(assert (set.member (tuple 2 3) x))
(assert (set.member (tuple 5 3) x))
(assert (set.member (tuple 3 9) x))
(assert (= z (rel.product x y)))
(assert (set.member (tuple 1 2 3 4) z))
(assert (not (set.member (tuple 5 9) x)))
(assert (set.member (tuple 3 8) y))
(assert (= y (rel.tclosure x)))
(assert (not (set.member (tuple 1 2) y)))
(check-sat)
