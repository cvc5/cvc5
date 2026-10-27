; EXPECT: sat
(set-logic QF_BVDT)
(declare-datatypes ((d 0)) (((c) (_c (s Bool)))))
(declare-const x d)
(check-sat-assuming ((ite (s c) (s x) (s x))))
