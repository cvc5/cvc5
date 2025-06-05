; EXPECT: unsat
(set-logic ALL)
(assert (= (str.to_int "0007") (- 1)))
(check-sat)
