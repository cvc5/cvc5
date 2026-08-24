; REQUIRES: no-safe-mode
; COMMAND-LINE: --solve-bv-as-int=bv
;; unsupported operator int.pow2
; DISABLE-TESTER: alethe
; EXPECT: unsat
(set-logic QF_BV)
(declare-fun s () (_ BitVec 4))
(declare-fun t () (_ BitVec 4))
(assert (not (= (bvlshr s (bvor (bvand t #b0000) s)) #b0000)))
(check-sat)
(exit)
