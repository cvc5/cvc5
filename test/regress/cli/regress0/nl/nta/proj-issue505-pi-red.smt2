; EXPECT: unsat
(set-logic ALL)
(assert (is_int (arcsin real.pi)))
(assert (= real.pi (cos real.pi)))
(check-sat)
