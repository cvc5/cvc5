; COMMAND-LINE: --cbqi-bv --cbqi-bv-ineq=keep --no-cbqi-full --bv-div-zero-const
; EXPECT: unsat
(set-logic BV)
(set-info :status unsat)
(declare-fun a () (_ BitVec 8))
(declare-fun b () (_ BitVec 8))

(assert (distinct a b (_ bv0 8)))
(assert (forall ((x (_ BitVec 8))) (= (bvudiv a x) b)))

(check-sat)
