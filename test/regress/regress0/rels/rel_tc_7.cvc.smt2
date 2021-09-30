; EXPECT: unsat
(set-option :incremental false)
(set-logic ALL)

(declare-fun x () (Set (Tuple Int Int)))
(declare-fun y () (Set (Tuple Int Int)))
(assert (= y (join (tclosure x) x)))
(assert (member (tuple 1 2) (join (join x x) x)))
(assert (not (subset y (tclosure x))))
(check-sat)
