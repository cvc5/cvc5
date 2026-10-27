; EXPECT: unsat
(set-logic QF_BV)
(declare-const v (_ BitVec 6))
(assert (and (bvugt v #b100000) (bvnego v)))
(check-sat)
