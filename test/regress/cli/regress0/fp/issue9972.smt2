; EXPECT: sat
; REQUIRES: no-assertions
; This regression test failed with a check-model failure prior to #10589 without
; assertions. With assertions, this fails with a spurious assertion failure in
; SymFPU. We thus, for now, only test this for builds without assertions.
(set-logic QF_BVFP)
(set-option :check-models true)
(declare-const a Float64)
(declare-const b Float64)
(assert (= (_ bv0 32) ((_ fp.to_sbv 32) RTZ b)))
(assert (bvuge ((_ fp.to_sbv 32) RTZ a) (_ bv1 32)))
(check-sat)
