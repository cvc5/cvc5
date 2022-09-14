; EXPECT: unknown
(set-logic ALL)
(set-option :full-saturate-quant true)
(declare-fun q2 (Real Real) Bool)
(assert (forall ((x2 Real)) (q2 x2 (ite (< x2 1.0) x2 1.0))))
(check-sat)
