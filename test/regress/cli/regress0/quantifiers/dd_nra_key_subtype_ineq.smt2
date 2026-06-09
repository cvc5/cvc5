; EXPECT: unsat
(set-logic ALL)
(declare-fun z () Real)
(assert (forall ((M Real)) (= M (/ 0.0 (* 2.0 z)))))
(check-sat)
