; REQUIRES: unrestricted-mode
; EXPECT: sat
(set-logic ALL)
(set-option :strings-exp true)
(assert (>= 0.0 (fp.to_real (seq.nth (seq.unit (fp (_ bv0 1) (_ bv0 8) (_ bv0 23))) 1))))
(check-sat)
