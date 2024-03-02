; COMMAND-LINE: --solve-bv-as-int=sum --bvand-integer-granularity=1
; COMMAND-LINE: --solve-bv-as-int=sum --bv-to-int-use-pow2 --bvand-integer-granularity=1
; EXPECT: unsat
;; unsupported int.pow2 operator
; DISABLE-TESTER: alethe
(set-logic QF_BV)
(declare-fun a () (_ BitVec 8))
(declare-fun b () (_ BitVec 8))
(assert (bvult (bvashr a b) (bvlshr a b)))

(check-sat)
