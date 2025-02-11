; DISABLE-TESTER: dump
; REQUIRES: no-competition
; EXPECT: The exponent of the POW(^) operator can only be a positive integral constant below 67108864
; SCRUBBER: grep -o "The exponent of the POW(^) operator can only be a positive integral constant below 67108864"
; EXIT: 1
(set-logic QF_BVNIA)
(declare-fun m () (_ BitVec 15))
(assert (= (_ bv0 1) (ite (> 1 (int.pow2 (bv2nat ((_ repeat 2) m)))) (_ bv1 1) (_ bv0 1))))
(check-sat)
