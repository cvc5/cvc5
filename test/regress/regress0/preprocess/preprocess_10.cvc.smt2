; EXPECT: sat
(set-logic ALL)
(set-option :incremental false)
(declare-fun x () Real)
(declare-fun b () Bool)
(assert (= x (ite b 10 (- 10))))
(assert b)
(check-sat)
