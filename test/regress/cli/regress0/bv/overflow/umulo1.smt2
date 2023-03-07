; EXPECT: unsat
(set-logic QF_BV)
(declare-const v (_ BitVec 6))
(assert (and (= (bvmul v v) (_ bv53 6)) (not (bvumulo v v))))
(check-sat)
