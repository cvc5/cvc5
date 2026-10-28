; REQUIRES: no-safe-mode
; COMMAND-LINE: --learned-rewrite
; EXPECT: unsat
; --learned-rewrite is not supported with proofs or unsat cores because
; the preprocessing pass does not track its non-local reasoning.
; DISABLE-TESTER: unsat-core
; DISABLE-TESTER: proof
(set-logic QF_NIA)
(declare-const x Int)
(declare-const y Int)
(assert (and (<= x 0) (< 0 y) (or (= 0 y) (> 0 (mod x y)))))
(check-sat)
