; COMMAND-LINE: --solve-bv-as-int=sum --mbqi
; EXPECT: unsat
(set-logic UFBV)
(declare-fun f ((_ BitVec 2)) (_ BitVec 4))
(declare-fun g ((_ BitVec 4)) (_ BitVec 2))
(assert (forall ((x (_ BitVec 4)) (y (_ BitVec 4))) (=> (distinct x y) (distinct (f (g x)) (f (g y))))))
(check-sat)
