; REQUIRES: unrestricted-mode
; EXPECT: unsat
(set-logic ALL)
(declare-const x Real)
(assert (= (arcsec (- 1.0)) 5.0))
(check-sat)
