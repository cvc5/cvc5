; REQUIRES: unrestricted-mode
; EXPECT: unknown
(set-logic ALL)
(declare-const x Real)
(assert (= (arcsec (- 1.0)) real.pi))
(check-sat)
