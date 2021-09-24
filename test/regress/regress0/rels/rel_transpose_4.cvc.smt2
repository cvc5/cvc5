; EXPECT: unsat
(set-option :incremental false)
(set-logic ALL)

(declare-fun x () (Set (Tuple Int Int)))
(declare-fun y () (Set (Tuple Int Int)))
(declare-fun z () (Tuple Int Int))
(assert (= z (mkTuple 1 2)))
(assert (member z x))
(assert (not (member (mkTuple 2 1) (transpose x))))
(check-sat)
