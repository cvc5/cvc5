; EXPECT: sat
(set-logic QF_BV)
(declare-const v (_ BitVec 6))
(assert (and (bvult v #b110000) (bvnego v)))
(check-sat)
