; COMMAND-LINE: --solve-bv-as-int=sum --bvand-integer-granularity=1
; COMMAND-LINE: --solve-bv-as-int=sum --bv-to-int-use-pow2 --bvand-integer-granularity=1
; COMMAND-LINE: --solve-bv-as-int=bitwise --bvand-integer-granularity=1
; COMMAND-LINE: --solve-bv-as-int=sum --bvand-integer-granularity=5
; COMMAND-LINE: --solve-bv-as-int=bitwise --bvand-integer-granularity=5
; COMMAND-LINE: --solve-bv-as-int=iand --iand-mode=value
; COMMAND-LINE: --solve-bv-as-int=iand --iand-mode=sum
; COMMAND-LINE: --solve-bv-as-int=bv
; EXPECT: unsat
(set-logic QF_BV)
(declare-fun s () (_ BitVec 4))
(declare-fun t () (_ BitVec 4))
(assert (not (= (bvlshr s (bvor (bvand t #b0000) s)) #b0000)))
(check-sat)
(exit)
