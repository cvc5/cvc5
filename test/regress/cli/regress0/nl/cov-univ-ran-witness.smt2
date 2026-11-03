; REQUIRES: poly
; COMMAND-LINE: --nl-cov --nl-ext=none
; EXPECT: unsat
; The covering endpoints are the irrational roots sqrt(2) and cbrt(3), which
; appear in the proof as REAL_ALGEBRAIC_NUMBER_WITNESS terms.
(set-logic QF_NRA)
(declare-fun x () Real)
(assert (< (* x x) 2.0))
(assert (> (* x x x) 3.0))
(check-sat)
