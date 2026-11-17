; REQUIRES: unrestricted-mode
; EXPECT: unknown
(set-logic UFNIRAT)
(assert (= (arccos (- 1.0)) real.pi))
(check-sat)
