; REQUIRES: unrestricted-mode
; COMMAND-LINE: --check-models
; EXPECT: sat
(set-logic ALL)
(declare-fun v () Int)
(declare-fun c () (_ FloatingPoint 8 24))
(assert (< v 33554432))
(assert (= c ((_ to_fp 8 24) roundNearestTiesToEven (to_real v))))
(assert (= c ((_ to_fp 8 24) roundNearestTiesToEven 33554432.0)))
(check-sat)
