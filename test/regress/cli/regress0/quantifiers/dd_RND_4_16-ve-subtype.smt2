; EXPECT: unsat
(set-logic ALL)
(declare-const x Real)
(assert (forall ((? Real)) (distinct 0.0 (+ ? x))))
(check-sat)
