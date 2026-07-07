; COMMAND-LINE: --solve-bv-as-int=sum --mbqi
; EXPECT: sat
(set-logic UFBV)
(declare-sort S 0)
(declare-fun f (S) (_ BitVec 16))
(assert (forall ((x S) (y S)) (= (f x) (f y))))
(check-sat)
