; EXPECT: sat
(set-logic ALL)
(declare-fun g (Real Real) Real)
(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun z () Real)
(assert (> x 3(g x y) 2  (/ 4444 (g x y)444 z x) (+ x 4z)))
(check-sat)
