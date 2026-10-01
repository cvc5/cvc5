; REQUIRES: unrestricted-mode
; COMMAND-LINE: -q --check-models
; EXPECT: sat
(declare-const x Float64)
(assert (distinct (_ bv0 32) (bvlshr ((_ extract 31 0) ((_ sign_extend 32) ((_ fp.to_sbv 32) RTZ x))) (_ bv0 32))))
(check-sat)
