; COMMAND-LINE: --check-proofs
; EXPECT: unsat
(set-logic QF_UFLIRA)
(declare-fun f (Real) Bool)
(declare-const p Int)
(assert (>= p 0))
(assert (not (>= p 1)))
(assert (f 0.0))
(assert (not (f (to_real p))))
(check-sat)
