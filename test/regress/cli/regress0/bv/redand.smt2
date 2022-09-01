; EXPECT: sat
(set-logic QF_BV)
(declare-const x (_ BitVec 3))
(declare-const y (_ BitVec 3))
(assert (= #b1 (bvor (bvredand x) (bvredand y))))
(check-sat)
