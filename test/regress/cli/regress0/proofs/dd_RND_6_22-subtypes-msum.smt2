; EXPECT: unsat
(set-logic ALL)
(declare-fun x () Real)
(assert
(forall ((y Real))
(and
(exists ((z Real)) false)
(exists ((w Real)) (= 0.0 (+ w 1.0 x))))))
(check-sat)
