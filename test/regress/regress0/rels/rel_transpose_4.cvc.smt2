; EXPECT: unsat
(set-option :incremental false)
(set-logic ALL)

(declare-fun x () (Set (Tuple Int Int)))
(declare-fun y () (Set (Tuple Int Int)))
(declare-fun z () (Tuple Int Int))
(assert (= z (tuple 1 2)))
(assert (set.member z x))
(assert (not (set.member (tuple 2 1) (rel.transpose x))))
(check-sat)
