; EXPECT: sat
(set-logic ALL)
(set-option :incremental false)
(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun b () Bool)
(assert (= 0.0 (ite b (- x y) (* 2.0 x))))
(check-sat)
