; REQUIRES: unrestricted-mode
; COMMAND-LINE:
; COMMAND-LINE: --check-proofs
; EXPECT: unsat
; The sign of a Real -> Float conversion is the sign of the argument, in every
; rounding mode and also when the conversion underflows to zero: a negative
; argument never yields +zero and a positive argument never yields -zero.
; Both are ruled out by the registration lemmas of TheoryFp::registerTerm
; only. The refinement lemmas of TheoryFp::refineAbstraction cannot rule them
; out, since they are formulated in terms of fp.leq/fp.geq and of the
; rationals the results denote, all of which identify -zero and +zero. Without
; the sign lemmas, the refinement detects the disagreement with the correct
; rounding but makes no progress, and the answer is unknown.
(set-logic QF_FPLRA)
(declare-const x Real)
(declare-const y Real)
(declare-const fx Float32)
(declare-const fy Float32)
(assert (= fx ((_ to_fp 8 24) RNE x)))
(assert (= fy ((_ to_fp 8 24) RTP y)))
(assert (< x 0.0))
(assert (> y 0.0))
(assert (or (fp.isPositive fx) (fp.isNegative fy)))
(check-sat)
