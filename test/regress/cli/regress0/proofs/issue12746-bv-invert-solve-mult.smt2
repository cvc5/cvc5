; EXPECT: unsat
(set-logic ALL)
(declare-const a (_ BitVec 4))
(declare-const t (_ BitVec 4))
(assert (distinct true (exists ((x (_ BitVec 4)))
        (= #b0001 (bvxor (bvadd x x x) a)))))
(check-sat)
