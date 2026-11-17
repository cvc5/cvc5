; REQUIRES: unrestricted-mode
; EXPECT: unsat
(set-logic ALL)
(set-option :fp-exp true)
(set-option :solve-bv-as-int sum)
(set-option :check-proof-steps true)
(declare-const x Float16)
(assert (fp.isPositive (fp.neg (fp.abs x))))
(check-sat)
