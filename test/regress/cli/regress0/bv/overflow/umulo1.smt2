; EXPECT: unsat
; COMMAND-LINE: 
; COMMAND-LINE: --solve-bv-as-int=sum
(set-logic QF_BV)
(declare-const v (_ BitVec 6))
(assert (and (= (bvmul v v) (_ bv53 6)) (not (bvumulo v v))))
(check-sat)
