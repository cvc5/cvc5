; EXPECT: unsat
(set-logic NRA)
(declare-const r0 Real)
(assert (exists ((q36 Real) (q37 Bool) (q38 Bool) (q39 Bool) (q40 Real) (q41 Bool)) (= 0.0 0.0 (/ 437686.0 r0) 0.0 0.96101)))
(check-sat)
