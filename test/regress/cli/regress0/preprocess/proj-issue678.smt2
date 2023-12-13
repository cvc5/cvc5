; EXPECT: unsat
(set-logic ALL)
(assert false)
(assert (<= real.pi (sec real.pi)))
(check-sat)
