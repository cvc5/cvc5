; EXPECT: unsat
(set-logic ALL)
(set-option :incremental false)
(declare-fun b () Bool)
(declare-datatypes ((D 0)) (((c (s Int)))))
(check-sat-assuming ( (not (= (c (ite b 1 0)) (ite b (c 1) (c 0)))) ))
