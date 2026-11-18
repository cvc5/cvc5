; REQUIRES: unrestricted-mode
; COMMAND-LINE: -q
; EXPECT: unsat
(set-logic ALL)
(set-option :check-proof-steps true)
(set-option :solve-bv-as-int iand)
(assert (<= real.pi (tan 1.0)))
(check-sat)
