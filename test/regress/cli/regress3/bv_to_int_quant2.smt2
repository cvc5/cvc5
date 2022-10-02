; COMMAND-LINE: --cegqi-all --full-saturate-quant --solve-bv-as-int=sum
; COMMAND-LINE: --cegqi-all --full-saturate-quant --solve-bv-as-int=bv
; COMMAND-LINE: --cegqi-all --full-saturate-quant --solve-bv-as-int=iand
; EXPECT: sat
(set-logic BV)
(declare-fun s () (_ BitVec 4))
(assert (bvult s (_ bv4 4)))
(assert (forall ((x (_ BitVec 4))) (= (bvand x s) (_ bv0 4))))
(check-sat)
(exit)
