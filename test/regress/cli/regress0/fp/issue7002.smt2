; EXPECT: sat
(set-logic ALL)
(assert (= 0.0 (fp.to_real (_ NaN 8 24))))
(check-sat)
