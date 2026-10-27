; EXPECT: sat
(set-logic QF_ABVFFLIA)
(declare-const x Bool)
(assert (= 0 (ite x 1 0)))
(check-sat)
