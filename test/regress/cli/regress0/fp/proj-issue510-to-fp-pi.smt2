; REQUIRES: unrestricted-mode
; EXPECT: unknown
(set-logic ALL)
(set-option :fp-exp true)
(assert (= ((_ to_fp 5 11) roundNearestTiesToAway real.pi) (fp (_ bv0 1) (_ bv0 5) (_ bv0 10))))
(check-sat)
