; REQUIRES: unrestricted-mode
; COMMAND-LINE:
; COMMAND-LINE: --check-unsat-cores
; EXPECT: unsat
; The quantified formula is false: any x large enough overflows to +oo, and
; then the body requires 0.0 >= x. Refuting it requires the refinement of the
; conversion abstraction to determine that the model's +oo value for the
; conversion means that x is at least the overflow threshold. Without that
; lemma the refinement walks the rounding cells of the finite floats one by
; one and never converges.
(set-logic ALL)
(assert (forall ((x Real))
  (>= 0.0 (ite (fp.isInfinite ((_ to_fp 8 24) RNE x)) x 0.0))))
(check-sat)
