; EXPECT: unsat
; COMMAND-LINE: 
(set-logic QF_BV)
(declare-const v (_ BitVec 6))
(assert (and (= v (_ bv53 6)) (not (bvsmulo v v))))
(check-sat)
