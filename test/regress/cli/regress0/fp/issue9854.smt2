; EXPECT: unsat
; REQUIRES: no-assertions
; This regression test failed with a check-model failure prior to #10589 without
; assertions. With assertions, this fails with a spurious assertion failure in
; SymFPU. We thus, for now, only test this for builds without assertions.
(set-logic BVFP)
(assert (forall ((n Float64)) (= (_ bv0 80) ((_ zero_extend 48) ((_ fp.to_sbv 32) roundNearestTiesToEven n)))))
(check-sat)
