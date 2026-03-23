; COMMAND-LINE: --solve-bv-as-int=sum --sygus-inst
; EXPECT: unsat
(set-logic UFBV)
(declare-fun f ((_ BitVec 1)) (_ BitVec 2))
(declare-fun g ((_ BitVec 2)) (_ BitVec 1))
(assert (forall ((x (_ BitVec 2))) (= (f (g x)) x)))
(check-sat)
