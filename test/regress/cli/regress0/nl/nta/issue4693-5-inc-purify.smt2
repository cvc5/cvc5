; EXPECT: unsat
(set-logic ALL)
(set-info :status unsat)
(assert (forall ((t Real)) (= 0.0 (/ t (cos 1.0)))))
(check-sat)
