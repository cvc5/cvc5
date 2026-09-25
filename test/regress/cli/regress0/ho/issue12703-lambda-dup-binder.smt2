; EXPECT: sat
(set-logic HO_ALL)
(declare-sort $ 0)
(declare-fun t () $)
(declare-fun p ($) Bool)
(assert (forall ((X $)) (and (@ (@ (lambda ((Y1 $) (Y1 $)) (p Y1)) (@ (lambda ((Z1 $)) Z1) t)) t))))
(check-sat)
