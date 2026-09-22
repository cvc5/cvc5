; EXPECT: unsat
(set-logic ALL)
(assert (forall ((x (_ BitVec 32))) (not (= (bvnot x) (_ bv0 32)))))
(check-sat)
