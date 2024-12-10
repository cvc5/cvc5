; EXPECT: unsat
(set-logic ALL)
(declare-datatypes ((d 0)) (((c (s Bool)) (_c (_s Bool)))))
(declare-const x d)
(assert (= ((_ is _c) x) ((_ is c) ((_ update _s) x true))))
(check-sat)
