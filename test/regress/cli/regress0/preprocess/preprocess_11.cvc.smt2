; EXPECT: sat
(set-logic ALL)
(set-option :incremental false)
(declare-fun x () Real)
(declare-fun y () Real)
(assert (and (and (and (= 0.0 (ite true x 1.0)) (= 0.0 (ite (= x 0.0) 0.0 1.0))) (= x (ite true y 0.0))) (= 0.0 (ite true 0.0 0.0))))
(check-sat)
