; REQUIRES: unrestricted-mode
; DISABLE-TESTER: alethe
; COMMAND-LINE: --macros-quant --macros-quant-mode=all --proof-granularity=dsl-rewrite --proof-check=eager
; EXPECT: unsat
(set-logic UFLIA)
(declare-fun P (Int) Bool)
(declare-fun Q (Int Int) Bool)
(assert (forall ((x Int)) (= (P x) (forall ((y Int)) (Q x y)))))
(assert (P 0))
(assert (not (Q 0 1)))
(check-sat)
