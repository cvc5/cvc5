; EXPECT: sat
(set-logic ALL)
(assert (= 0.0 (/ 0.0 (to_real (to_real 0)))))
(check-sat)
