; REQUIRES: no-safe-mode
; COMMAND-LINE: --incremental --macros-quant --proof-granularity=dsl-rewrite --proof-check=eager
; EXPECT: unsat
; EXPECT: unsat
; EXPECT: unsat
(set-logic UFLIA)
(declare-fun P (Int) Bool)
(declare-fun Q (Int) Bool)
(push 1)
(assert (forall ((x Int)) (P x)))
(assert (not (P 0)))
(check-sat)
(pop 1)
; The same symbol receives a different definition after pop.
(push 1)
(assert (forall ((x Int)) (not (P x))))
(assert (P 0))
(check-sat)
(pop 1)
; Check dependencies through two macro substitutions.
(push 1)
(assert (forall ((x Int)) (= (P x) (Q x))))
(assert (forall ((x Int)) (Q x)))
(assert (not (P 0)))
(check-sat)
(pop 1)
