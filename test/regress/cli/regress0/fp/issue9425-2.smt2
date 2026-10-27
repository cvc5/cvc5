; REQUIRES: unrestricted-mode
; EXPECT: sat
(set-logic ALL)
(assert (= (_ -oo 2 3) (fp #b1 #b11 #b00)))
(check-sat)
