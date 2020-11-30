; COMMAND-LINE: --ext-rewrite-quant
; EXPECT: sat
(set-logic UFLIA)
(set-info :status sat)
(declare-fun Q (Int Int) Bool)
(assert (forall ((x Int)) (or (and (or (Q 0 x) (Q 1 x)) (Q 2 x)) (not (Q 2 x)) (not (Q 1 x)))))
(check-sat)
