; EXPECT: unsat
(set-logic ALL)
(assert (and (exists ((R Int)) (exists ((x Int)) (and false (forall ((R Int) (R Int)) true))))))
;(assert (not (forall ((R Int) (R Int)) true)))
(check-sat)
