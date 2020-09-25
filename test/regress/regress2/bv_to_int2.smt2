; COMMAND-LINE: --solve-bv-as-int=sum --bvand-integer-granularity=1
; COMMAND-LINE: --solve-bv-as-int=sum --bvand-integer-granularity=5
; COMMAND-LINE: --solve-bv-as-int=sum --bvand-integer-granularity=8
; EXPECT: sat
(set-logic QF_BV)
(declare-fun a () (_ BitVec 8))
(declare-fun b () (_ BitVec 8))
(assert (bvult (bvshl a b) (bvlshr a b)))

(check-sat)
