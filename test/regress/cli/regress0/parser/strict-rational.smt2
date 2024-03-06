; EXPECT: sat
(set-logic QF_LIRA)
(declare-fun x () Real)
(declare-fun -2 () Real)
(assert (= x 3))
(assert (= x -2))
(check-sat)
