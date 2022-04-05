; EXPECT: sat
(set-logic QF_UFLRAFS)
(set-info :status sat)
(declare-fun x () (Set Real))
(declare-fun y () (Set Real))
(assert (not (= x y)))
(check-sat)
