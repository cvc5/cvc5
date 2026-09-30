; REQUIRES: unrestricted-mode
; COMMAND-LINE: -q --no-debug-check-models
; EXPECT: sat
;
; The secant planes for exp are built from the polynomial approximation
; P(x)/(1-x^n/n!), which is an upper bound for exp(x) only where its
; denominator is positive. This was ensured for the center of the secant
; planes but not for their end points, where the approximation can evaluate to
; a value far below exp (even a negative one), yielding unsound secant lemmas.
;
; Note that we disable debug model checking since it does not terminate for
; models that assign irrational values to transcendental functions.
(set-logic ALL)
(declare-fun v () Real)
(assert (< v 2.0))
(assert (> (+ (sin v) (exp v)) 6.0))
(check-sat)
