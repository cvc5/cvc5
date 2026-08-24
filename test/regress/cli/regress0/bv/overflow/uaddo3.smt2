; EXPECT: unsat
; COMMAND-LINE: 
(set-logic QF_BV)
(declare-const v (_ BitVec 6))
(assert (and (bvugt v (_ bv53 6)) (not (bvuaddo v v))))
(check-sat)
