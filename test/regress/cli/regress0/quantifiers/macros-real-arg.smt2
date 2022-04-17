; COMMAND-LINE: --macros-quant
; EXPECT: unsat
; this will fail if type rule for APPLY_UF is made strict
(set-logic UFLIRA)
(declare-fun P (Int) Bool)
(declare-fun Q (Int) Bool)
(assert (and (forall ((x Int)) (P x)) (forall ((x Int)) (Q x))))
(declare-fun k () Real)
(declare-fun k2 () Int)
(assert (or (not (P (to_int k))) (not (P k2))))
(assert (= k 0.0))
(check-sat)
