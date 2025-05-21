; EXPECT: unsat
(set-logic ALL)
(declare-fun x () Real)
(assert (or
(not (= (csc x) (/ 1.0 (sin x))))
(not (= (sec x) (/ 1.0 (cos x))))
))
(check-sat)
