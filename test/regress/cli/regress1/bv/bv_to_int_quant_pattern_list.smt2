; COMMAND-LINE: --solve-bv-as-int=sum --mbqi
; EXPECT: sat
(set-logic UFBV)
(declare-fun f ((_ BitVec 4)) (_ BitVec 4))
(assert (forall ((x (_ BitVec 4)))
  (! (= (f (bvneg x)) (f (bvnot x)))
     :pattern ((bvneg x) (bvnot x))
     :pattern ((bvneg x)))))
(check-sat)
