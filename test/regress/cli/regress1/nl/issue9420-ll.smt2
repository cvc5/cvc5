; REQUIRES: no-safe-mode
; COMMAND-LINE: --learned-rewrite
; EXPECT: unsat
; --learned-rewrite is not supported with proofs or unsat cores because
; the preprocessing pass does not track its non-local reasoning.
; DISABLE-TESTER: unsat-core
; DISABLE-TESTER: proof
(set-logic AUFBVFPDTNIRA)

(declare-const x Int)
(declare-const y Int)

(assert (not (= y 0)))
(assert (not (= (mod x y) (mod x (abs y)))))

(check-sat)
