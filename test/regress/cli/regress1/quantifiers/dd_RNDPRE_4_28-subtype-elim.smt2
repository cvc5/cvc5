; EXPECT: unsat
(set-logic ALL)
(declare-const x1 Bool)
(assert (forall ((? Real)) (exists ((x Real)) (and x1 (< ? 0)))))
(check-sat)
