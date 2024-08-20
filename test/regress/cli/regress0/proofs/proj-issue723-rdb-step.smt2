; EXPECT: unsat
(set-logic ALL)
(declare-const x (_ BitVec 1))
(set-option :check-proof-steps true)
(assert (bvult (_ bv0 10) (bvxor ((_ zero_extend 9) x) ((_ zero_extend 9) x))))
(check-sat)
