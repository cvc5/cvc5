; EXPECT: unsat
(set-logic ALL)
(declare-const __ (_ BitVec 1))
(set-option :check-proofs true)
(assert (set.is_singleton (set.insert (_ bv0 101) ((_ zero_extend 100) __) (set.singleton (_ bv1 101)))))
(check-sat)
