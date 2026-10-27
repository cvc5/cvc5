; EXPECT: unsat
(set-logic ALL)
(declare-const _x (_ BitVec 1))
(declare-const s (_ BitVec 64))
(declare-const t (_ BitVec 64))
(assert (distinct (= (bvxor s t) (bvand (bvxor s t) ((_ zero_extend 63) _x))) (exists ((x (_ BitVec 64))) (and (= t (bvxor x s)) (= x (bvand x ((_ zero_extend 63) _x)))))))
(check-sat)
