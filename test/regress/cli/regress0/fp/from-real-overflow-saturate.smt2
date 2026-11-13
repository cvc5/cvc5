; REQUIRES: unrestricted-mode
; EXPECT: unsat
; The rounding modes that round towards zero never overflow to an infinity,
; and the directed modes only overflow to the infinity they round towards, so
; no real converts to the infinities below.
(set-logic ALL)
(declare-const x Real)
(declare-const y Real)
(declare-const z Real)
(assert (or (fp.isInfinite ((_ to_fp 8 24) RTZ x))
            (and (fp.isInfinite ((_ to_fp 8 24) RTN y))
                 (fp.isPositive ((_ to_fp 8 24) RTN y)))
            (and (fp.isInfinite ((_ to_fp 8 24) RTP z))
                 (fp.isNegative ((_ to_fp 8 24) RTP z)))))
(check-sat)
