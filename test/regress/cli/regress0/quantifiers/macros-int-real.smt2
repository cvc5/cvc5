; COMMAND-LINE: --macros-quant
; EXPECT: unknown
(set-logic AUFLIRA)

(declare-fun round2 (Real) Int)
(assert (forall ((i Int))  (= (round2 (to_real i)) i)))

(assert (= (round2 1.5) 1))
(check-sat)