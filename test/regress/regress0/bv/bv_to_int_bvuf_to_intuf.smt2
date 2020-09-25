; COMMAND-LINE: --solve-bv-as-int=sum --bvand-integer-granularity=1
; EXPECT: sat
(set-logic QF_UFBV)
(declare-fun a () (_ BitVec 4))
(declare-fun b () (_ BitVec 4))
(declare-fun f ((_ BitVec 4)) (_ BitVec 4) )
(assert (distinct (bvadd a b) (f a)))
(check-sat)
