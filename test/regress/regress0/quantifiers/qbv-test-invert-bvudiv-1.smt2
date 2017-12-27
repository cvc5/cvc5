; COMMAND-LINE: --cbqi-bv --cbqi-bv-ineq=keep --no-cbqi-full --bv-div-zero-const
; EXPECT: sat
(set-logic BV)
(set-info :status sat)
(declare-fun a () (_ BitVec 8))
(declare-fun b () (_ BitVec 8))

(assert (distinct a b (_ bv0 8)))
(assert (forall ((x (_ BitVec 8))) (not (= (bvudiv a x) b))))

(check-sat)
