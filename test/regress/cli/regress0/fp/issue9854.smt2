; EXPECT: unsat
(set-logic BVFP)
(assert (forall ((n Float64)) (= (_ bv0 80) ((_ zero_extend 48) ((_ fp.to_sbv 32) roundNearestTiesToEven n)))))
(check-sat)
