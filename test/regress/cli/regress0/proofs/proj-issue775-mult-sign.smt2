; EXPECT: unsat
(set-logic ALL)
(declare-fun x () Real)
(assert (< (* (/ 0.0 (- 0.0 x)) (* x x)) 0.0))
(check-sat)
