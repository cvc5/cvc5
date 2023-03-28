; EXPECT: sat
(set-logic ALL)
(assert (forall ((t Int)) (<= 0.0 (* 1.0 (^ 0 1.0)))))
(check-sat)
