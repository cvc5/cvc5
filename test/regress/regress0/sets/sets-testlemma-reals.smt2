; EXPECT: sat
(set-logic QF_UFLRA_SETS)
(set-info :status sat)
(declare-fun x () (Set Real))
(declare-fun y () (Set Real))
(assert (not (= x y)))
(check-sat)
(get-model)
