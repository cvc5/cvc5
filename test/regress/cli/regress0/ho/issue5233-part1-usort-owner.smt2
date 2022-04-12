; EXPECT: sat
(set-logic HO_QF_AUFBVLIA)
(declare-fun a (Int) Int)
(declare-fun b (Int) Int)
(assert (distinct a b))
(check-sat)
