; REQUIRES: unrestricted-mode
; EXPECT: unsat
(set-logic ALL)
(set-option :check-proof-steps true)
(check-sat-assuming ((>= 1.0 (* real.pi real.pi))))
