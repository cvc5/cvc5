; EXPECT: sat
(set-logic ALL)
(assert (= 1.0 (exp 0.0)))
(check-sat)
