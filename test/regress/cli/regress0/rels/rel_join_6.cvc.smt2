; EXPECT: unsat
(set-option :incremental false)
(set-logic ALL)

(declare-fun x () (Relation Int Int))
(declare-fun y () (Relation Int Int))
(declare-fun r () (Relation Int Int))
(assert (= x (set.union (set.singleton (tuple 1 2)) (set.singleton (tuple 3 4)))))
(assert (= y (rel.join x (set.union (set.singleton (tuple 2 1)) (set.singleton (tuple 4 3))))))
(assert (not (set.member (tuple 1 1) y)))
(check-sat)
