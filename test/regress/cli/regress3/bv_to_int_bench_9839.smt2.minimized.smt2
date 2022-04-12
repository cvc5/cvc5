; COMMAND-LINE:  --solve-bv-as-int=bv
; COMMAND-LINE:  --bvand-integer-granularity=1 --solve-bv-as-int=sum
; COMMAND-LINE:  --bvand-integer-granularity=1 --solve-bv-as-int=bitwise
; EXPECT: sat
(set-logic QF_BV)
(declare-fun _substvar_1171_ () (_ BitVec 32))
(assert (bvsge ((_ sign_extend 0) _substvar_1171_) (_ bv0 32)))
(check-sat)
(exit)
