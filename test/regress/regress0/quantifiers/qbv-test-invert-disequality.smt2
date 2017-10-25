; COMMAND-LINE: --cbqi-bv --cbqi-bv-ineq=keep
; EXPECT: sat
(set-logic BV)
(set-info :status sat)
(declare-fun a () (_ BitVec 32))
(declare-fun b () (_ BitVec 32))

(assert (forall ((x (_ BitVec 32))) (= (bvand x a) b)))

(check-sat)
