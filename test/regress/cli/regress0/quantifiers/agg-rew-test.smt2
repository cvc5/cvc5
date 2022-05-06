; COMMAND-LINE: --ext-rewrite-quant
; EXPECT: sat
(set-logic UFLIA)
(set-info :status sat)
(declare-fun Q (Int Int) Bool)
(assert (forall ((x Int)) (=> (Q 0 x) (or (ite (Q 0 x) (not (Q 2 x)) (Q 3 x)) (Q 2 x)))))
(check-sat)
