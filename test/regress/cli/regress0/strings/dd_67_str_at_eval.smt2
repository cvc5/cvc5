; EXPECT: unsat
(set-logic ALL)
(assert (>= (ite (str.prefixof "" (str.at "" 0)) 0 0) 1))
(check-sat)
