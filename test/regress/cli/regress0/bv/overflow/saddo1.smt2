; EXPECT: unsat
; COMMAND-LINE: 
; COMMAND-LINE: --solve-bv-as-int=sum
(set-logic QF_BV)
(declare-const v (_ BitVec 6))
(assert (and (bvsgt v (_ bv32 6)) (not (bvsaddo v v))))
(check-sat)
