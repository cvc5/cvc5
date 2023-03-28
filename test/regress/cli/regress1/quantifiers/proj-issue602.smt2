; EXPECT: unsat
(set-logic ALL)
(set-option :ieval use)
(assert (forall ((x RoundingMode)) (distinct (= RTZ x) (distinct x roundNearestTiesToEven))))
(check-sat)
