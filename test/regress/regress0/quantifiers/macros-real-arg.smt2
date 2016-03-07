; COMMAND-LINE: --macros-quant
; EXPECT: unsat
; this will fail if type rule for APPLY_UF is made strict
(set-logic UFLIRA)
(declare-fun P (Int) Bool)
(assert (forall ((x Int)) (P x)))
(declare-fun k () Real)
(declare-fun k2 () Int)
(assert (or (not (P k)) (not (P k2))))
(assert (= k 0))
(check-sat)
