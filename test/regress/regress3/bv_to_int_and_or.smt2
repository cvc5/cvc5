; COMMAND-LINE: --solve-bv-as-int=sum --bvand-integer-granularity=1  
; COMMAND-LINE: --solve-bv-as-int=sum --bvand-integer-granularity=2  
; EXPECT: unsat
(set-logic QF_BV)
(declare-fun a () (_ BitVec 4))
(declare-fun b () (_ BitVec 4))
(assert (bvult (bvor a b) (bvand a b)))
(check-sat)
