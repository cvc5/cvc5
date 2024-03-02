; EXPECT: unsat
;; Logic not supported in Alethe
; DISABLE-TESTER: alethe
(set-logic ALL)
(declare-const x (Seq Real))
(check-sat-assuming ((= x (seq.++ x (seq.unit 0.0))) (= x (seq.++ x (seq.unit 0.0)))))
