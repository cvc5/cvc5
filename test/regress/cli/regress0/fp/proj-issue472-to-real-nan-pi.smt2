; REQUIRES: unrestricted-mode
; EXPECT: unknown
(set-logic ALL)
(assert (= real.pi (fp.to_real (fp (_ bv0 1) (_ bv255 8) (_ bv1 23)))))
(check-sat)
