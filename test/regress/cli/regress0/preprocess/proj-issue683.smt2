; EXPECT: unsat
(set-logic ALL)
(check-sat-assuming (false (= (- 0.0) 0.0)))
