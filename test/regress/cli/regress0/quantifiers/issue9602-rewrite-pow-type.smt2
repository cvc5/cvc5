; EXPECT: sat
(set-logic ALL)
(assert (forall ((t Int)) (<= 0.0 (* 1.0 (^ 0 1.0)))))
(assert (forall ((t Int)) (<= 0.0 (* 1.0 (^ 2 1.0)))))
(assert (forall ((t Int)) (<= 0.0 (* 1.0 (^ 3 3.0)))))
(check-sat)
