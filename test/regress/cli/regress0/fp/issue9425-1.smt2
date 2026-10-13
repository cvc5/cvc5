; REQUIRES: unrestricted-mode
; COMMAND-LINE: --fp-exp
; EXPECT: unsat
(set-logic QF_AFP)
(assert (distinct (_ bv0 1) ((_ extract 32 32) ((_ fp.to_sbv 33) roundNearestTiesToEven ((_ to_fp 27 6) roundNearestTiesToEven (fp (_ bv0 1) (_ bv0 13) (_ bv0 2)))))))
(check-sat)
