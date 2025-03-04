; EXPECT: unsat
(set-logic ALL)
(declare-const a (_ BitVec 4))
(declare-const t (_ BitVec 4))
(assert (distinct true (exists ((x (_ BitVec 4))) (= (_ bv0 4) (bvxor (bvadd #b0001 x a) t)))))
(check-sat)
