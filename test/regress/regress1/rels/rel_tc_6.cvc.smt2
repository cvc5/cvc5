; EXPECT: unsat
(set-option :incremental false)
(set-logic ALL)

(declare-fun x () (Set (Tuple Int Int)))
(declare-fun y () (Set (Tuple Int Int)))
(assert (= y (tclosure x)))
(assert (not (subset (join (join x x) x) y)))
(check-sat)
