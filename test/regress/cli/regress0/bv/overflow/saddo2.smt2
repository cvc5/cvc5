; EXPECT: sat
(set-logic QF_BV)
(declare-const v (_ BitVec 3))
(assert (not (bvsaddo v v)))
(check-sat)
