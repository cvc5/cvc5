; EXPECT: unsat
(set-option :incremental false)
(set-logic ALL)

(declare-fun x () (Set (Tuple Int Int)))
(declare-fun y () (Set (Tuple Int Int)))
(declare-fun r () (Set (Tuple Int Int)))
(assert (= x (union (singleton (mkTuple 1 2)) (singleton (mkTuple 3 4)))))
(assert (= y (join x (union (singleton (mkTuple 2 1)) (singleton (mkTuple 4 3))))))
(assert (not (member (mkTuple 1 1) y)))
(check-sat)
