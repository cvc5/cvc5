; EXPECT: sat
(set-logic ALL)
(set-option :incremental false)
(declare-datatypes ((pair 2)) ((par (T1 T2)((mkpair (first T1) (second T2))))))
(declare-fun x () (pair Bool Bool))
(assert (= x (mkpair true true)))
(check-sat)
