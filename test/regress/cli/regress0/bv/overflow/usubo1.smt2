; EXPECT: unsat
(set-logic QF_BV)
(declare-const v (_ BitVec 6))
(assert (and (= (bvsub v v) (_ bv53 6)) (not (bvusubo v v))))
(check-sat)
