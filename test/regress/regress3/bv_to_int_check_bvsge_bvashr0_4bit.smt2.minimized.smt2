; COMMAND-LINE:  --solve-bv-as-int=bv  --no-check-models
; COMMAND-LINE:  --cegqi-all --full-saturate-quant --bvand-integer-granularity=1 --solve-bv-as-int=sum      --no-check-models
; COMMAND-LINE:  --cegqi-all --full-saturate-quant --bvand-integer-granularity=1 --solve-bv-as-int=iand --iand-mode=sum     --no-check-models
; COMMAND-LINE:  --cegqi-all --full-saturate-quant --bvand-integer-granularity=1 --solve-bv-as-int=iand --iand-mode=bitwise     --no-check-models
; COMMAND-LINE:  --cegqi-all --full-saturate-quant --bvand-integer-granularity=1 --solve-bv-as-int=iand     --no-check-models
; COMMAND-LINE:  --cegqi-all --full-saturate-quant --bvand-integer-granularity=2 --solve-bv-as-int=sum      --no-check-models
; EXPECT: sat
(set-logic BV)
(declare-fun s () (_ BitVec 3))
(declare-fun t () (_ BitVec 3))
(define-fun min () (_ BitVec 3) (_ bv0 3))
(define-fun SC ((s (_ BitVec 3)) (t (_ BitVec 3))) Bool (bvsge (_ bv0 3) t))
(assert (not (and (=> (SC s t) (exists ((x (_ BitVec 3))) (bvsge (bvashr x s) t))) (=> (exists ((x (_ BitVec 3))) (bvsge (bvashr x s) t)) (SC s t)))))
(check-sat)
(exit)
