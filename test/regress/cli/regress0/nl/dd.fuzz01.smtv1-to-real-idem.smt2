; EXPECT: sat
(set-logic QF_UFNRA)
(set-info :status sat)
(declare-fun f (Real) Real)
(declare-fun p (Real Real Real) Bool)
(check-sat-assuming ((= 0.0 (/ 1 (ite (p 0.0 0.0 (/ (ite (p 0.0 0.0 (f 0.0)) 1 0) 1)) 1 0)))))
