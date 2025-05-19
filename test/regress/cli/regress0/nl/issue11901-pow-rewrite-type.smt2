; EXPECT: unsat
(set-logic ALL)
(assert (distinct 0 (^ 0 4.0))) 
(check-sat)
