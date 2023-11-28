; EXPECT: sat
(set-logic NIA)
(set-option :ext-rewrite-quant true)
(set-info :status sat)
(declare-fun v4 () Bool)
(declare-fun v92 () Bool)
(assert (forall ((q688 Bool)) (or v4 (and v92 q688))))
(check-sat)
