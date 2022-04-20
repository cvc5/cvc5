; EXIT: 1
; EXPECT: (error "The exponent of the POW(^) operator can only be a positive integral constant below 67108864. Exception occurred in:
; EXPECT:  (^ 3 x)")
(set-logic ALL)
(set-option :incremental false)
(declare-fun x () Int)
(assert (= (^ 3 x) 27))
(check-sat-assuming ( (= x 3) ))
