; REQUIRES: unrestricted-mode
; EXPECT: unsat
(set-logic ALL)
(declare-const x Real)
(assert (= (arctan x) (/ real.pi 2.0)))
(check-sat)
