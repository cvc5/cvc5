; COMMAND-LINE: --solve-bv-as-int=sum --bvand-integer-granularity=1
; EXPECT: sat
(set-logic QF_UFBV)
(declare-sort S 0)
(declare-fun s () S)
(declare-fun a () (_ BitVec 4))
(declare-fun b () (_ BitVec 4))
(declare-fun f ((_ BitVec 4)) (_ BitVec 4) )
(declare-fun g (S) (_ BitVec 4))
(declare-fun h ((_ BitVec 4)) S)
(assert (distinct (bvadd a b) (f a)))
(assert (distinct (f a) (g s)))
(assert (distinct (h a) s))
(check-sat)
