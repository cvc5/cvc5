; REQUIRES: unrestricted-mode
; EXPECT: unsat
(set-logic ALL)
(set-option :check-proofs true)
(set-option :proof-pedantic 9)
(assert (not true))
(check-sat)
