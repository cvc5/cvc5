(set-logic UFLIRA)
(set-info :status unsat)
; ensure that E-matching matches on sub-types
(declare-fun P (Real) Bool)
(assert (forall ((x Real)) (P x)))
(assert (not (P 5.0)))
(check-sat)
