; COMMAND-LINE: --bv-solver=bitblast-internal
; EXPECT: unsat
(set-logic ALL)
(declare-const __ (_ BitVec 3))
(declare-const ___ (_ BitVec 3))
(assert (= (_ bv0 64) (bvand (_ bv1 64) ((_ zero_extend 32) ((_ zero_extend 16) ((_ zero_extend 8) ((_ zero_extend 4) ((_ zero_extend 1) __))))))))
(assert (bvule __ ___))
(assert (= (_ bv0 64) (bvand (_ bv1 64) (bvadd (_ bv1 64) ((_ zero_extend 32) ((_ zero_extend 16) ((_ zero_extend 8) ((_ zero_extend 4) ((_ zero_extend 1) ___)))))))))
(assert (bvule ___ __))
(check-sat)
