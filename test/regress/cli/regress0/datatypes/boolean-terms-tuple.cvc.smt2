; EXPECT: sat
(set-logic ALL)
(set-option :incremental false)
(declare-fun x () (Tuple Int Bool))
(assert (not (= x (tuple 0 false))))
(check-sat)
