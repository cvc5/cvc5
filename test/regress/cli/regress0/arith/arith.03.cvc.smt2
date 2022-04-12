; EXPECT: unsat
(set-logic ALL)
(set-option :incremental false)
(declare-fun x () Real)
(declare-fun y () Real)
(check-sat-assuming ( (not (let ((_let_1 (+ x y))) (= (* _let_1 _let_1) (+ (+ (* x x) (* (* 2.0 x) y)) (* y y))))) ))
