; EXPECT: unsat
(set-logic ALL)
(declare-const x Real)
(declare-const x3 Real)
(assert (exists ((z Real)) (exists ((y Real)) (exists ((w Real)) 
(forall ((? Real)) (and (exists ((? Real)) false) (exists ((? Real)) (= 0.0 (+ ? x x3)))))))))
(check-sat)
