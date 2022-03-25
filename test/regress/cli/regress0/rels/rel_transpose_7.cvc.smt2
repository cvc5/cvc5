; EXPECT: unsat
(set-option :incremental false)
(set-logic ALL)

(declare-fun x () (Set (Tuple Int Int)))
(declare-fun y () (Set (Tuple Int Int)))
(assert (= x y))
(assert (not (= (rel.transpose x) (rel.transpose y))))
(check-sat)
