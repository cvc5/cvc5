; EXPECT: sat
(set-logic QF_BVSLIA)
(declare-fun s () String)
(declare-fun m () (_ BitVec 32))
(assert (= "0" (str.substr s 1 (ubv_to_int m))))
(check-sat)
