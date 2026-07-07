; EXPECT: unsat
(set-logic ALL)
(declare-const t (_ BitVec 4))
(assert (distinct true (exists ((x (_ BitVec 4))) (= (_ bv0 4) (bvxor x t)))))
(check-sat)
