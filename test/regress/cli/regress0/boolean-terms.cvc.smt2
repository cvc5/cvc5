; EXPECT: sat
(set-logic ALL)
(set-option :incremental false)
(declare-fun f (Bool) Int)
(declare-fun x () Int)
(declare-fun p (Bool) Bool)
(assert (= (f (p true)) x))
(assert (= (f (p false)) (+ x 1)))
(check-sat)
