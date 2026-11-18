; REQUIRES: unrestricted-mode
; EXPECT: unsat
(set-logic ALL)
(declare-const x Real)
(assert (and (>= x 2.0) (= (arcsec x) (/ real.pi 2.0))))
(check-sat)
