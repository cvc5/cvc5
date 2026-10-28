; REQUIRES: unrestricted-mode
; EXPECT: sat
(set-logic ALL)
(assert (>= (fp.to_real ((_ to_fp 8 24) (seq.nth (seq.unit (_ bv0 32)) (seq.len (seq.unit (_ bv0 32)))))) (fp.to_real (fp (_ bv0 1) (_ bv255 8) (_ bv1 23)))))
(check-sat)
