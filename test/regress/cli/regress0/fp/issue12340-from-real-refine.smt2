; EXPECT: sat
(set-logic ALL)
(assert (forall ((d Float32)) (= (fp (_ bv1 1) (_ bv0 11) (_ bv0 52)) ((_ to_fp 11 53) RNE (fp.to_real ((_ to_fp 8 24) (bvlshr ((_ fp.to_sbv 32) RNE (fp (_ bv0 1) (_ bv255 8) (_ bv1 23))) (_ bv1 32))))))))
(check-sat)
