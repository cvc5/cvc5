; EXPECT: unsat
(set-option :incremental false)
(set-logic ALL)

(declare-fun x () (Set (Tuple Int Int)))
(declare-fun e () (Tuple Int Int))
(assert (= e (mkTuple 4 4)))
(assert (member e x))
(assert (not (member (mkTuple 4 4) x)))
(check-sat)
