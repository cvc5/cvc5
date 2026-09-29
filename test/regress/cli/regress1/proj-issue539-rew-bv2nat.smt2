; EXPECT: unsat
(set-logic ALL)
(declare-const __ (_ BitVec 1))
(assert (< (ubv_to_int ((_ zero_extend 37) __)) (- (ubv_to_int ((_ zero_extend 37) __)))))
(check-sat)
