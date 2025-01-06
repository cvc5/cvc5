; EXPECT: unsat
(set-logic ALL)
(assert (= (str.from_int 123) "124"))
(check-sat)
