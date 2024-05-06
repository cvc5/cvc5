; EXPECT: sat
; EXPECT: unsat

(set-logic UFBV)
(set-option :incremental true)
(set-option :solve-bv-as-int sum)
(set-option :full-saturate-quant true)
(set-option :finite-model-find true)

(declare-fun f ((_ BitVec 4)) (_ BitVec 4))

(assert (forall ((x (_ BitVec 4))) (= (f x) (_ bv0 4))))
(check-sat)
(push 1)
(assert (forall ((y (_ BitVec 4))) (= (f y) (_ bv1 4))))
(check-sat)
(pop 1)

