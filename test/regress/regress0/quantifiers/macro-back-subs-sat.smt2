; COMMAND-LINE: --macros-quant
; EXPECT: sat
(set-logic UFLIA)
(declare-fun A (Int) Int)
(declare-fun B (Int) Int)
(declare-fun C (Int) Int)

(assert (forall ((x Int)) (= (A x) (C (B x)))))
(assert (forall ((x Int)) (= (B x) 0)))

(assert (= (A 3) (B 4)))

(check-sat)
