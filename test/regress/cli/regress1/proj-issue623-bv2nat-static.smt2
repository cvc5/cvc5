; EXPECT: sat
(set-logic ALL)
(declare-const __ (_ BitVec 1))
(assert (distinct (seq.unit (_ bv0 20)) (seq.at (seq.unit (_ bv0 20)) (int.pow2 (+ (ubv_to_int ((_ zero_extend 19) __)) (ubv_to_int ((_ zero_extend 19) __)) (ubv_to_int ((_ zero_extend 19) __)))))))
(assert (>= (int.pow2 (+ (ubv_to_int ((_ zero_extend 19) __)) (ubv_to_int ((_ zero_extend 19) __)) (ubv_to_int ((_ zero_extend 19) __)))) (+ (ubv_to_int ((_ zero_extend 19) __)) (ubv_to_int ((_ zero_extend 19) __)))))
(check-sat)
