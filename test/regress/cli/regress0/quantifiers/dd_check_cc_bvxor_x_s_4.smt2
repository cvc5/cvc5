; EXPECT: unsat
(set-logic ALL)
(assert (distinct true (exists ((x (_ BitVec 4)) (s (_ BitVec 4))) (= (bvxor x s) (_ bv0 4)))))
(check-sat)
