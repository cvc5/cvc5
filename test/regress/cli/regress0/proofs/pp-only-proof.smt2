; EXPECT: unsat
(set-logic ALL)
(set-option :proof-mode pp-only)
(set-option :check-proofs true)
(check-sat-assuming (false))
