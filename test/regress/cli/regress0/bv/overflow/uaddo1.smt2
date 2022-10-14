; EXPECT: unsat
(set-logic QF_BV)
(declare-const v (_ BitVec 6))
(assert (and (= (bvadd v v) (_ bv53 6)) (not (bvuaddo v v))))
(check-sat)
