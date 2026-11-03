; REQUIRES: unrestricted-mode
; COMMAND-LINE: --check-models
; EXPECT: sat
(set-logic ALL)
(declare-fun r () Real)
(declare-fun c () (_ FloatingPoint 8 24))
(assert (< r 2.0))
(assert (= c ((_ to_fp 8 24) roundNearestTiesToEven r)))
(assert (= c (fp #b0 #x80 #b00000000000000000000000)))   ; c == 2.0
(check-sat)
