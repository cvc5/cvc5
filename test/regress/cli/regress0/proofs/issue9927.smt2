; EXPECT: unsat
(set-logic QF_LRA)
(declare-fun b () Bool)
(assert (= 0.0 (ite b 2.0 1.0)))
(check-sat)