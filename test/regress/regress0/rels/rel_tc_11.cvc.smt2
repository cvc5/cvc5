; EXPECT: unsat
(set-option :incremental false)
(set-logic ALL)


(declare-fun x () (Set (Tuple Int Int)))
(declare-fun y () (Set (Tuple Int Int)))
(declare-fun z () (Set (Tuple Int Int Int Int)))
(assert (member (mkTuple 2 3) x))
(assert (member (mkTuple 5 3) x))
(assert (member (mkTuple 3 9) x))
(assert (= z (product x y)))
(assert (member (mkTuple 1 2 3 4) z))
(assert (not (member (mkTuple 5 9) x)))
(assert (member (mkTuple 3 8) y))
(assert (= y (tclosure x)))
(assert (not (member (mkTuple 1 2) y)))
(check-sat)
