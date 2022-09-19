; EXPECT: sat
; EXPECT: (((/ x 0) 6.0))
(set-logic ALL)
(set-option :produce-models true)
(declare-fun x () Int)
(assert (= (/ x 0) 6))
(check-sat)
(get-value ((/ x 0)))
