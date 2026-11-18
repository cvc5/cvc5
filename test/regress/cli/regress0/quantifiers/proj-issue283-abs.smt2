; EXPECT: unsat
(set-logic ALL)
(assert (forall ((v Int)) (= 0 (abs v))))
(check-sat)
