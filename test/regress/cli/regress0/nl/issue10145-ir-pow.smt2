; REQUIRES: unrestricted-mode
; EXPECT: sat
(set-logic ALL)
(assert (= 0.0 (^ 0.0 4.0)))
(check-sat)
