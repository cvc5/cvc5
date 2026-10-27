; EXPECT: unsat
(set-logic ALL)
(assert (= 0 (div 0 0)))
(assert (not (= 0 (div 0 0 0))))
(check-sat)

