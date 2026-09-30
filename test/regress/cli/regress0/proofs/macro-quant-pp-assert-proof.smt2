; REQUIRES: no-safe-mode
; COMMAND-LINE: --proof-granularity=dsl-rewrite --proof-check=eager
; EXPECT: unsat
(set-logic UFLIA)
(set-option :macros-quant true)

(declare-fun P (Int) Bool)

(assert (forall ((x Int)) (P x)))
(assert (not (P 0)))

(check-sat)
