; EXPECT: unsat
(set-option :incremental false)
(set-logic ALL)

(declare-fun x () (Set (Tuple Int Int)))
(declare-fun y () (Set (Tuple Int Int)))
(assert (member (tuple 2 2) (tclosure x)))
(assert (= x (as emptyset (Set (Tuple Int Int)))))
(check-sat)
