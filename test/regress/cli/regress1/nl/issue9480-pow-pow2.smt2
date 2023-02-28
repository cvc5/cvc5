; SCRUBBER: sed -e 's/(error.*/error/; s/(^.*//'
; EXPECT: error
; EXIT: 1
(set-logic QF_UFLRA)
(declare-fun f4 () Real)
(declare-fun ___ (Real Real) Real)
(assert (= 0.0 (^ (- (- 2.0)) (___ (/ f4 2.0) 1.0))))
(check-sat)
