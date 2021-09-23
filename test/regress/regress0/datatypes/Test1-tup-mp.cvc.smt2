; EXPECT: sat
(set-logic ALL)
(set-option :incremental false)

(declare-fun test (Int) (Tuple Int Int))
(assert (= (test 5) (mkTuple 2 3)))
(assert (= (test 7) (mkTuple 3 4)))
(check-sat)
