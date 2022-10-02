; COMMAND-LINE: --incremental --mbqi
(set-logic UFLIA)
(declare-fun P (Int) Bool)
(declare-fun R (Int) Bool)
(assert (forall ((x Int)) (=> (R x) (not (P x)))))
; EXPECT: sat
(check-sat)
(assert (R 0))
; EXPECT: sat
(check-sat)
(assert (forall ((x Int)) (P x)))
; EXPECT: unsat
(check-sat)
(push 1)
; EXPECT: unsat
(check-sat)
