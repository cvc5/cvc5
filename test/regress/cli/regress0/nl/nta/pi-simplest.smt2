; EXPECT: unsat
(set-logic ALL)
(assert (= real.pi 1.0))
(check-sat)
