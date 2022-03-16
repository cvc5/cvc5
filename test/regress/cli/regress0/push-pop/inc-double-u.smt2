; COMMAND-LINE: --incremental 
(set-logic UFLIA)
(declare-fun P (Int) Bool)
(declare-fun R (Int) Bool)
(assert (forall ((x Int)) (=> (R x) (not (P x)))))
; EXPECT: unknown
(check-sat)
(assert (R 0))
; EXPECT: unknown
(check-sat)
(assert (forall ((x Int)) (P x)))
; EXPECT: unsat
(check-sat)
(push 1)
; EXPECT: unsat
(check-sat)
