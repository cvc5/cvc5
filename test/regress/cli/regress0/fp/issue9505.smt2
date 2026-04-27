; COMMAND-LINE: --fp-exp
; EXPECT: sat
(set-logic QF_FP)
(declare-fun m () (_ FloatingPoint 4 12))
(assert (fp.eq (fp (_ bv0 1) (_ bv0 8) (_ bv0 23)) ((_ to_fp 8 24) roundNearestTiesToEven (fp.rem m (fp (_ bv0 1) (_     bv9 4) (_ bv1536 11))))))
(check-sat)
