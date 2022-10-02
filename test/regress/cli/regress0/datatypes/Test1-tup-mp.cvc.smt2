; EXPECT: sat
(set-logic ALL)
(set-option :incremental false)

(declare-fun test (Int) (Tuple Int Int))
(assert (= (test 5) (tuple 2 3)))
(assert (= (test 7) (tuple 3 4)))
(check-sat)
