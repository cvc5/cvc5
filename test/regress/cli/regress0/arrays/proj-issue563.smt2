; SCRUBBER: sed -e 's/((f.*/((f/g'
; EXPECT: sat
; EXPECT: ((f
(set-logic ALL)
(set-option :produce-models true)
(define-fun f ((_f1_2 RoundingMode) (_f1_4 Bool)) RoundingMode (ite _f1_4 _f1_2 RTZ))
(check-sat)
(get-value (f))
