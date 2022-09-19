; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(assert (= 1.0 (* (/ 0.0 0.0) (/ 0.0 0.0) (/ 1.0 0.0))))
(check-sat)
