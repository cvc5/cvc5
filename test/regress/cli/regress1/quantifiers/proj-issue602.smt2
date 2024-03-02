; EXPECT: unsat
;; Logic not supported in Alethe
; DISABLE-TESTER: alethe
(set-logic ALL)
(set-option :ieval use)
(assert (forall ((x RoundingMode)) (distinct (= RTZ x) (distinct x roundNearestTiesToEven))))
(check-sat)
