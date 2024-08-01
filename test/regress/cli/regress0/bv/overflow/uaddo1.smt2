; EXPECT: unsat
(set-logic QF_BV)
(declare-const v (_ BitVec 6))
(assert (and (ugt v (_ bv32 6)) (not (bvuaddo v v))))
(check-sat)
