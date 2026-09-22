; EXPECT: unsat
(set-logic ALL)
(assert (exists ((? Int)) (and false (exists ((? Int)) (forall ((? Int) (? Int)) false)))))
(check-sat)
