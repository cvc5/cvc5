; EXPECT: unsat
(set-option :incremental false)
(set-logic ALL)

(declare-fun x () (Set (Tuple Int Int)))
(declare-fun y () (Set (Tuple Int Int)))
(declare-fun z () (Set (Tuple Int Int)))
(assert (or (= z (transpose y)) (= z (transpose x))))
(assert (not (= (transpose z) y)))
(assert (not (= (transpose z) x)))
(check-sat)
