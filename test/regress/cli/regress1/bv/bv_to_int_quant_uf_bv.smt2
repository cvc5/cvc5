; COMMAND-LINE: --solve-bv-as-int=iand --finite-model-find
; EXPECT:
; SCRUBBER: grep -v "uninterpreted"
; EXIT: 1
(set-logic UFBV)
(declare-sort S 0)
(declare-fun f (S) (_ BitVec 16))
(assert (forall ((x S) (y S)) (= (f x) (f y))))
(check-sat)
