; EXPECT: unsat
(set-option :incremental false)
(set-logic ALL)

(declare-fun x () (Set (Tuple Int Int)))
(declare-fun y () (Set (Tuple Int Int)))
(declare-fun r () (Set (Tuple Int Int)))
(assert (= x (union (singleton (tuple 1 2)) (singleton (tuple 3 4)))))
(assert (= y (join x (union (singleton (tuple 2 1)) (singleton (tuple 4 3))))))
(assert (not (member (tuple 1 1) y)))
(check-sat)
