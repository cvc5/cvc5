; REQUIRES: unrestricted-mode
; EXPECT: unknown
(set-logic ALL)
(assert (<= (fp.to_real (_ +oo 8 24)) real.pi (fp.to_real (_ +oo 8 24))))
(check-sat)
