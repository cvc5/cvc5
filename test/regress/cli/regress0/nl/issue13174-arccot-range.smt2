; REQUIRES: unrestricted-mode
; EXPECT: unsat
(set-logic ALL)
(declare-const x Real)
(assert (= (arccot x) 0.0))
(check-sat)
