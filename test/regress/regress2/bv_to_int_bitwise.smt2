; COMMAND-LINE: --solve-bv-as-int=sum --bvand-integer-granularity=1 --no-check-unsat-cores
; COMMAND-LINE: --solve-bv-as-int=bitwise --bvand-integer-granularity=1 --no-check-unsat-cores
; COMMAND-LINE: --solve-bv-as-int=sum --bvand-integer-granularity=5 --no-check-unsat-cores
; COMMAND-LINE: --solve-bv-as-int=bitwise --bvand-integer-granularity=5 --no-check-unsat-cores
; COMMAND-LINE: --solve-bv-as-int=iand --iand-mode=value --no-check-unsat-cores
; COMMAND-LINE: --solve-bv-as-int=iand --iand-mode=sum --no-check-unsat-cores
; COMMAND-LINE: --solve-bv-as-int=bv --no-check-unsat-cores
; EXPECT: unsat
(set-logic QF_BV)
(declare-fun s () (_ BitVec 4))
(declare-fun t () (_ BitVec 4))
(assert (not (= (bvlshr s (bvor (bvand t #b0000) s)) #b0000)))
(check-sat)
(exit)
