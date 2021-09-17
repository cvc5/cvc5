; EXPECT: sat
(set-option :incremental false)
(set-logic ALL)

(declare-fun x () (Set (Tuple Int Int)))
(declare-fun y () (Set (Tuple Int Int)))
(declare-fun z () (Set (Tuple Int Int)))
(assert (member (mkTuple 1 3) x))
(assert (or (member (mkTuple 2 3) z) (member (mkTuple 2 1) z)))
(assert (= y (transpose x)))
(assert (not (member (mkTuple 1 2) y)))
(assert (= x z))
(check-sat)
