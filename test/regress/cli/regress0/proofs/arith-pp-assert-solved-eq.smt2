; COMMAND-LINE: --proof-granularity=theory-rewrite --check-proofs -o trusted-proof-steps
; SCRUBBER: grep -E ':trust-id SUBS_EQ'
; EXIT: 0
;
; The equalities below are solved by TheoryArithPrivate::ppAssert, which
; requires normalizing them first, since the rewriter does not normalize
; equalities. This tests that the resulting substitutions x -> 1 and y -> 0 are
; proven based on polynomial normalization, and not by a trusted (SUBS_EQ)
; step. Note the expected output is empty, i.e. the proof contains no such step.
(set-logic ALL)
(declare-const x Int)
(declare-const y Int)
(assert (= (+ x 1) 2))
(assert (= (to_real y) 0.0))
(assert (< (+ x y) 0))
(check-sat)
