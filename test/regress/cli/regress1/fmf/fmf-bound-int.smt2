; COMMAND-LINE: --finite-model-find --fmf-bound
; EXPECT: sat
(set-logic UFLIA)
(declare-fun P (Int Int) Bool)
(declare-fun Q (Int) Bool)
(assert (forall ((x Int)) (=> (and (<= 0 x) (<= x (ite (P 0 0) 10 20))) (Q x))))
(check-sat)
