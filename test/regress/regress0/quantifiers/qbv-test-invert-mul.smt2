(set-logic BV)
(set-info :status sat)
(declare-fun a () (_ BitVec 32))
(declare-fun b () (_ BitVec 32))
(declare-fun c () (_ BitVec 32))

(assert (forall ((x (_ BitVec 32))) (not (= (bvmul x a) b))))

(check-sat)
