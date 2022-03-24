; EXPECT: unsat
(set-option :incremental false)
(set-logic ALL)

(declare-fun x () (Set (Tuple Int Int)))
(declare-fun y () (Set (Tuple Int Int)))
(assert (set.member (tuple 2 2) (rel.tclosure x)))
(assert (= x (as set.empty (Set (Tuple Int Int)))))
(check-sat)
