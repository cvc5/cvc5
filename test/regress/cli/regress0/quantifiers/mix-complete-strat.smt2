; COMMAND-LINE: --cegqi --finite-model-find
; EXPECT: sat
(set-logic UFLIA)
(set-info :status sat)

(declare-sort U 0)
(declare-fun P (U) Bool)

(assert (forall ((x U)) (P x)))

(declare-fun u () U)
(assert (P u))

(declare-const a Int)
(declare-const b Int)
(assert (forall ((x Int)) (or (> x a) (< x b))))

(check-sat)
