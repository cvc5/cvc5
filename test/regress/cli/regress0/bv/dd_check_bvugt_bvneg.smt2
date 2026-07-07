; EXPECT: unsat
(set-logic ALL)
(declare-const t (_ BitVec 1))
(assert (forall ((x (_ BitVec 4))) (not (bvugt x ((_ zero_extend 3) t)))))
(check-sat)
