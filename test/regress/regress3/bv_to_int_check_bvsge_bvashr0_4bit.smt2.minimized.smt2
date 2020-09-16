; COMMAND-LINE:  --cegqi-all --full-saturate-quant --bvand-integer-granularity=1 --solve-bv-as-int=sum
; COMMAND-LINE:  --cegqi-all --full-saturate-quant --bvand-integer-granularity=2 --solve-bv-as-int=sum
; EXPECT: sat
(set-logic BV)
(declare-fun s () (_ BitVec 3))
(declare-fun t () (_ BitVec 3))
(assert (not (and (=> (bvsge (_ bv0 3) t) (exists ((x (_ BitVec 3))) (bvsge (bvashr x s) t))) (=> (exists ((x (_ BitVec 3))) (bvsge (bvashr x s) t)) (bvsge (_ bv0 3) t)))))
(check-sat)
(exit)
