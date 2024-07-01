; EXIT: 1
; EXPECT: (error "The exponent of the POW(^) operator can only be a positive integral constant below 67108864. Exception occurred in:
; EXPECT:   (^ 2 (- 2))")
(set-logic ALL)
(declare-fun x () Int)
(assert (and (= (* (^ 2 x) (- 4 x)) (+ (* 2 x) 4))  (= x (- 0 2))))
(check-sat)
(get-model)
