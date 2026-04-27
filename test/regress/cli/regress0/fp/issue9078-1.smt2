; EXPECT: sat
(set-logic ALL)
(declare-const x (_ FloatingPoint 11 53))
(declare-const y (_ BitVec 54))
(define-fun t () (_ FloatingPoint 11 53)  ((_ to_fp_unsigned 11 53) roundNearestTiesToAway y))
(assert (not (= x t)))
(check-sat)
(exit)
