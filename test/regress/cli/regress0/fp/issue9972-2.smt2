; EXPECT: sat
(set-logic QF_BVFP)
(set-option :check-models true)
(declare-const a Float64)
(declare-const b Float64)
(assert (not (= (_ bv0 32) (bvlshr ((_ extract 31 0) ((_ sign_extend 32) ((_ fp.to_sbv 32) RTZ a))) ((_ extract 31 0) ((_ sign_extend 32) ((_ fp.to_sbv 32) RTZ b)))))))
(check-sat)
