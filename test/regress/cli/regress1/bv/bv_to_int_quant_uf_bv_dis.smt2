; COMMAND-LINE: --solve-bv-as-int=sum --full-saturate-quant
; EXPECT: unsat
(set-logic UFBV)
(declare-sort S 0)
(declare-fun f (S) (_ BitVec 2))
(assert (exists ((x1 S) (x2 S) (x3 S) (x4 S) (x5 S)) (distinct x1 x2 x3 x4 x5)))
(assert (forall ((x S) (y S)) (=> (distinct x y) (distinct  (f x) (f y)))))
(check-sat)
