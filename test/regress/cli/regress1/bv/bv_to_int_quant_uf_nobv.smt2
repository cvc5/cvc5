; COMMAND-LINE: --solve-bv-as-int=iand --finite-model-find
; EXPECT: sat
(set-logic UFBV)
(declare-sort S 0)
(declare-fun f ((_ BitVec 16)) S)
(assert (forall ((x (_ BitVec 16)) (y (_ BitVec 16))) (= (f x) (f y))))
(check-sat)
