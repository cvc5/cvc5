; REQUIRES: no-safe-mode
; DISABLE-TESTER: alethe
; COMMAND-LINE: --macros-quant --proof-granularity=dsl-rewrite --proof-check=eager
; EXPECT: unsat
(set-logic UFLIA)
(declare-fun P (Int) Bool)
(declare-fun Q (Int) Bool)
(assert (forall ((x Int)) (= (not (P x)) (Q x))))
(assert (= (P 0) (Q 0)))
(check-sat)
