; EXPECT: unsat
; REQUIRES: no-safe-mode
; COMMAND-LINE:
; COMMAND-LINE: --solve-bv-as-int=sum
(set-logic QF_BV)
(declare-const v (_ BitVec 6))
(assert (and (= (bvmul v v) (_ bv53 6)) (not (bvsmulo v v))))
(check-sat)
