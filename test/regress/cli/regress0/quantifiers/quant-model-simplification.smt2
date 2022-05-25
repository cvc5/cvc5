; COMMAND-LINE: --finite-model-find
; EXPECT: sat
(set-logic UFLIA)
(set-info :status sat)
(declare-sort U 0)
(declare-fun b () Int)
(declare-fun P (U) Bool)
(assert (= b (ite (forall ((x U)) (P x)) 2 3)))
(check-sat)
