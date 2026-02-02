; EXPECT: unsat
(set-logic ALL)
(assert (exists ((R Int)) (exists ((x Int)) (and false (forall ((R Int) (R Int)) true)))))
(check-sat)
