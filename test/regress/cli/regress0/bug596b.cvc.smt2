; EXPECT: sat
(set-logic ALL)
(set-option :incremental false)
(declare-fun f (Int) (Tuple Int Bool))
(declare-fun a () Int)
(assert (not (= (f a) (tuple 0 false))))
(check-sat)
