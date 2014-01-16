; EXPECT: unsat
(set-logic ALL_SUPPORTED)
(declare-datatypes (T1 T2) ((Pair (mk-pair (first T1) (second T2)))))
(assert (= (mk-pair 0.0 0.0) (mk-pair 1.5 2.5)))
(check-sat)
(exit)
