; EXPECT: sat
(set-logic ALL)
(set-option :check-unsat-cores true)
(set-option :proof-mode sat-proof)
(set-option :incremental true)
(declare-const x String)
(declare-const x3 String)
(assert (not (str.<= x3 x)))
(check-sat-assuming (true))
