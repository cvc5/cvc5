; REQUIRES: unrestricted-mode
; EXPECT: unknown
(set-logic UFNIRAT)
(assert (= (arcsin (- 1.0)) (- (/ real.pi 2.0))))
(check-sat)
