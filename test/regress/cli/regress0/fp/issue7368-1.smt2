; REQUIRES: unrestricted-mode
; EXPECT: sat
(set-logic ALL)
(set-option :produce-models true)
(set-option :check-models true)
(declare-const d Float32)
(assert (distinct ((_ fp.to_sbv 4) RTP d) ((_ fp.to_sbv 4) RTN d)))
(check-sat)
