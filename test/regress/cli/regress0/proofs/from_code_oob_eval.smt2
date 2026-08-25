; EXPECT: unsat
(set-logic ALL)
(assert (= (str.from_code 1000000) "a"))
(check-sat)
