; EXPECT: unsat
(set-logic ALL)
(declare-const x (Seq Real))
(check-sat-assuming ((= x (seq.++ x (seq.unit 0.0))) (= x (seq.++ x (seq.unit 0.0)))))
