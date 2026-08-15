; EXPECT: unsat
; The Real -> Float -> Real round trip is idempotent: rounding an already
; rounded value does not change it, since fp.to_real is exact and rounding an
; exactly representable real returns it (for every rounding mode). Asserting
; the negation is therefore unsatisfiable.
;
; This is well defined here because to_fp from Real never yields NaN and 1/3
; does not overflow Float32, so fp.to_real is applied to finite floats only
; (for arguments that may be infinite, the round trip goes through the
; unconstrained undefined value of fp.to_real_total and is not idempotent).
;
; Note: idempotence is stated over the Reals on purpose. The corresponding
; float-level identity  f = to_fp(RNE, fp.to_real(f))  is NOT valid: for
; f = -zero it yields +zero, and = on floats is structural equality, so that
; version is satisfiable. Over the Reals both zeros denote 0 and the issue
; disappears.
;
; Note: x is pinned by two inequalities rather than by an equality on purpose.
; With (= x (/ 1 3)) the rewriter constant folds both conversions away and the
; abstraction refinement is never invoked -- the test would then only cover
; constant folding. Keep it as is. The nested (rt (rt x)) additionally covers
; the nested-conversion purification in TheoryFp::registerTerm.
(set-logic QF_FPLRA)
(declare-const x Real)
(define-fun rt ((v Real)) Real (fp.to_real ((_ to_fp 8 24) RNE v)))
(assert (>= x (/ 1 3)))
(assert (<= x (/ 1 3)))
(assert (not (= (rt x) (rt (rt x)))))
(check-sat)
