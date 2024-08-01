; EXPECT: unsat
; COMMAND-LINE: 
; COMMAND-LINE: --solve-bv-as-int=sum
(set-logic QF_BV)
(declare-const v (_ BitVec 6))
(assert (and (ugt v (_ bv32 6)) (not (bvuaddo v v))))
(check-sat)
