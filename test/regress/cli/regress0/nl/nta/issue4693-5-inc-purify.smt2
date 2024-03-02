; EXPECT: unsat
;; Logic not supported in Alethe
; DISABLE-TESTER: alethe
(set-logic ALL)
(set-info :status unsat)
(assert (forall ((t Real)) (= 0.0 (/ t (cos 1.0)))))
(check-sat)
