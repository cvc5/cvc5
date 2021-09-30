; EXIT: 1
; EXPECT: (error "The exponent of the POW(^) operator can only be a positive integral constant below 67108864. Exception occurred in:
; EXPECT:   (^ x 67108864)")
(set-logic ALL)
(set-option :incremental false)
(declare-fun x () Int)
(assert (= (^ x 67108864) 8))
(check-sat-assuming ( (= x 3) ))
