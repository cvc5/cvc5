; REQUIRES: unrestricted-mode
; EXPECT: unsat
(set-logic ALL)
(declare-const x Real)
(assert (and (>= x 2.0) (= (arccsc x) 0.0)))
(check-sat)
