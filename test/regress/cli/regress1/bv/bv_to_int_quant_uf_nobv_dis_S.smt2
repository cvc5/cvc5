; COMMAND-LINE: --solve-bv-as-int=sum --mbqi
; EXPECT: unsat
(set-logic UFBV)
(declare-sort S 0)
(declare-fun f ((_ BitVec 4)) S)
(assert (exists ((x1 S) (x2 S)) (and (distinct x1 x2) (forall ((y S)) (or (= y x1) (= y x2))))))
(assert (forall ((x (_ BitVec 4)) (y (_ BitVec 4))) (=> (distinct x y) (distinct (f x) (f y)))))
(check-sat)
