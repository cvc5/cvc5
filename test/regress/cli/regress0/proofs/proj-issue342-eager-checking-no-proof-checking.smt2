; EXPECT: unsat
(set-logic ALL)
(set-option :produce-unsat-cores true)
(set-option :proof-check eager)
(assert false)
(check-sat)