; COMMAND-LINE: --solve-bv-as-int=sum --mbqi
; EXPECT: unsat
(set-logic ALL)
(declare-fun f ((_ BitVec 128)) (_ BitVec 128))
(assert (forall ((A (_ BitVec 128))) (forall ((V (_ BitVec 128))) (= A (f V)))))
(check-sat)
