; EXPECT: sat
; EXPECT: ((((_ to_fp 5 11) roundNearestTiesToAway (/ 1 10)) (fp #b0 #b01011 #b1001100110)))
(set-logic ALL)
(set-option :produce-models true)
(check-sat)
(get-value (((_ to_fp 5 11) RNA 0.1)))
