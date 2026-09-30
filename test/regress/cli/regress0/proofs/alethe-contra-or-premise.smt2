; EXPECT: unsat
; Tests the Alethe translation of CONTRA when the premise for the
; contradicted formula is a disjunction whose proof concludes the
; corresponding clause rather than the unit clause with the disjunction. The
; atoms contain an operator changed by the Alethe conversion (mod becomes
; mod_total internally), so that the test of whether the disjunction is used
; as a singleton clause must compare the resolution pivot modulo conversion.
(set-logic QF_NIA)
(declare-fun v1 () Int)
(declare-fun v2 () Int)
(assert (not (or (or (>= (mod v1 3) 1) (>= (mod v2 3) 1)) (and (not (or (>= (mod v1 3) 1) (>= (mod v2 3) 1))) (or (or (>= (mod v1 3) 1) (>= (mod v2 3) 1)) (not (or (>= (mod v1 3) 1) (>= (mod v2 3) 1))))))))
(check-sat)
