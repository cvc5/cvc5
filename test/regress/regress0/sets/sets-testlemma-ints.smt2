; EXPECT: sat
(set-logic QF_UFLIA_SETS)
(set-info :status sat)
(declare-fun x () (Set Int))
(declare-fun y () (Set Int))
(assert (= x y))
(check-sat)
