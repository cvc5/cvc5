; COMMAND-LINE:  --solve-bv-as-int=bv -q
; COMMAND-LINE:  --bvand-integer-granularity=1 --solve-bv-as-int=sum --full-saturate-quant --cegqi-all -q
;EXPECT: sat
(set-logic BV)
(assert (exists ((c__detect__main__1__i_36_C (_ BitVec 32))) (bvslt ((_ sign_extend 32) c__detect__main__1__i_36_C) (_ bv0 64))))
(check-sat)
(exit)
