; EXPECT: sat
(set-logic ALL)
(set-option :incremental false)
(declare-fun x () (Tuple Int Bool))
(assert (not (= x (mkTuple 0 false))))
(check-sat)
