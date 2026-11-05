; REQUIRES: unrestricted-mode
; COMMAND-LINE: --learned-rewrite
; EXPECT: unsat
; --learned-rewrite is not supported with proofs or unsat cores because
; the preprocessing pass does not track its non-local reasoning.
; DISABLE-TESTER: unsat-core
; DISABLE-TESTER: proof
(set-logic QF_NIA)
(declare-const A Int)
(declare-const B Int)
(declare-const C Int)
(define-fun lemma () Bool (= (mod (+ (mod A (int.pow2 C)) B) (int.pow2 C)) (mod (+ A B) (int.pow2 C))))

(assert (> C 0))

(assert (not lemma))
(check-sat)
