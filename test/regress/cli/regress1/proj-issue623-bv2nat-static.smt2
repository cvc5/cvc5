; EXPECT: sat
(set-logic ALL)
(declare-const __ (_ BitVec 1))
(assert (distinct (seq.unit (_ bv0 20)) (seq.at (seq.unit (_ bv0 20)) (int.pow2 (+ (bv2nat ((_ zero_extend 19) __)) (bv2nat ((_ zero_extend 19) __)) (bv2nat ((_ zero_extend 19) __)))))))
(assert (>= (int.pow2 (+ (bv2nat ((_ zero_extend 19) __)) (bv2nat ((_ zero_extend 19) __)) (bv2nat ((_ zero_extend 19) __)))) (+ (bv2nat ((_ zero_extend 19) __)) (bv2nat ((_ zero_extend 19) __)))))
(check-sat)
