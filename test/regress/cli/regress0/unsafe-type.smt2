; EXPECT: unsat
(set-logic ALL)
(declare-const a (Array RoundingMode Int))
(declare-const b (Array RoundingMode Int))
(assert false)
(assert (= a b))
(check-sat)
