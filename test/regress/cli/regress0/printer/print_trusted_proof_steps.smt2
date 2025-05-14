; COMMAND-LINE: --proof-granularity=theory-rewrite --check-proofs -o trusted-proof-steps
; SCRUBBER: grep -E '\(trusted-proof-step'
; EXPECT: (trusted-proof-step (= (= 0 1) false) :rule TRUST_THEORY_REWRITE :theory THEORY_ARITH)
; REQUIRES: no-safe-mode
; We disable testing safe-mode since we are intentionally forcing a proof hole, which is an error in safe builds.
(set-logic ALL)
(set-option :dump-proofs true)
(assert (= 0 1))
(check-sat)
