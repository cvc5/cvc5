; COMMAND-LINE: --cbqi-bv --bv-div-zero-const
; EXPECT: sat
(set-logic BV)
(set-info :status sat)
(declare-fun a () (_ BitVec 16))
(declare-fun b () (_ BitVec 16))

(assert (distinct a b (_ bv0 16)))
(assert (forall ((x (_ BitVec 16))) (not (= (bvudiv x a) b))))

(check-sat)
