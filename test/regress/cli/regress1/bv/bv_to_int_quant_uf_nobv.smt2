; COMMAND-LINE: --solve-bv-as-int=sum --mbqi 
; EXPECT: sat
(set-logic UFBV)
(declare-sort S 0)
(declare-fun f ((_ BitVec 16)) S)
(assert (forall ((x (_ BitVec 16)) (y (_ BitVec 16))) (= (f x) (f y))))
(check-sat)
