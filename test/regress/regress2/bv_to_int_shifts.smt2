; COMMAND-LINE: --solve-bv-as-int=sum --bvand-integer-granularity=1
; COMMAND-LINE: --solve-bv-as-int=sum --bvand-integer-granularity=1 --bv-to-int-use-pow2
; EXPECT: sat
(set-logic QF_BV)
(declare-fun s () (_ BitVec 4))
(declare-fun t () (_ BitVec 4))
(declare-fun splust () (_ BitVec 4))
(declare-fun shift1 () (_ BitVec 4))
(declare-fun shift2 () (_ BitVec 4))
(declare-fun negshift1 () (_ BitVec 4))

(assert (= shift1 (bvlshr s splust)))
(assert (= shift2 (bvlshr t splust)))
(assert (= negshift1 (bvneg shift1)))
(assert (= splust (bvadd s t)))
(assert (distinct negshift1 shift2))
(assert (distinct s (bvshl s (_ bv4 4))))

(check-sat)
