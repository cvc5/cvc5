; COMMAND-LINE:  --cegqi-all --full-saturate-quant --bvand-integer-granularity=1 --solve-bv-as-int=sum 
; COMMAND-LINE:  --cegqi-all --full-saturate-quant --bvand-integer-granularity=1 --solve-bv-as-int=sum  --bv-to-int-use-pow2
; EXPECT: unsat
(set-logic BV)
(declare-fun s () (_ BitVec 4))
(assert (bvult s (_ bv4 4)))
(assert (forall ((x (_ BitVec 4))) (= (bvlshr x s) (_ bv0 4))))
(check-sat)
(exit)
