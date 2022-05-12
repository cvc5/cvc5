; COMMAND-LINE: --var-ineq-elim-quant
; EXPECT: unknown
(set-logic UFLIRA)

(declare-fun round2 (Real) Int)

(assert (forall ((x Real) (i Int)) (=> (<= x (to_real i)) (<= (round2 x) i)) ))
(assert (forall ((x Real) (i Int)) (=> (<= (to_real i) x) (<= i (round2 x))) ))


(check-sat)
