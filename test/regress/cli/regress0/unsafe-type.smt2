; EXPECT: unsat
(set-logic ALL)
(declare-const a RoundingMode)
(declare-const b RoundingMode)
(assert false)
(assert (= a b))
(check-sat)
