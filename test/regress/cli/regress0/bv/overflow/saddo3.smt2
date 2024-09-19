; COMMAND-LINE: 
; COMMAND-LINE: --solve-bv-as-int=sum
; EXPECT: unsat
(set-logic QF_BV)
(declare-const v (_ BitVec 6))
(assert (and (bvsgt v (_ bv28 6)) (not (bvsaddo v v))))
(check-sat)
