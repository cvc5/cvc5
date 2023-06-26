; EXPECT: unsat
(set-logic ALL)
(declare-const __ (_ BitVec 1))
(assert (< (bv2nat ((_ zero_extend 37) __)) (- (bv2nat ((_ zero_extend 37) __)))))
(check-sat)
