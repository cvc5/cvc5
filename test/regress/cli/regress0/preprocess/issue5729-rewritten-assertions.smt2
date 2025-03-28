; EXPECT: sat
(set-logic QF_ALL)
(declare-fun x () (_ BitVec 1))
(assert (= (_ bv0 1) ((_ int_to_bv 1) (ubv_to_int x))))
(check-sat)
