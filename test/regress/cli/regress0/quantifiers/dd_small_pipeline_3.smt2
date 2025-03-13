; EXPECT: unsat
(set-logic ALL)
(assert (exists ((V (_ BitVec 32))) (and (= (_ bv0 32) (bvadd V (_ bv1 32))) (= V (_ bv0 32)))))
(check-sat)
