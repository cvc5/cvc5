; COMMAND-LINE: --solve-bv-as-int=sum --bvand-integer-granularity=1 --no-check-models  --no-check-unsat-cores
; COMMAND-LINE: --solve-bv-as-int=sum --bvand-integer-granularity=8 --no-check-models  --no-check-unsat-cores
; EXPECT: unsat
(set-logic QF_BV)
(declare-fun a () (_ BitVec 8))
(declare-fun b () (_ BitVec 8))
(assert (bvult (bvashr a b) (bvlshr a b)))

(check-sat)
