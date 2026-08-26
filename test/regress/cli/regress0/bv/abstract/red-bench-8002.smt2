; COMMAND-LINE: --bv-abstraction
; EXPECT: sat
; Ported from Bitwuzla test/regress/solver/abstract/red-bench-8002.smt2
(set-logic QF_BV)
(set-info :status sat)
(declare-const __ (_ BitVec 4))
(declare-const T1 (_ BitVec 1))
(declare-fun T () (_ BitVec 8))
(declare-fun T1@ () (_ BitVec 8))
(assert (not (= (bvadd ((_ zero_extend 24) T) (bvmul (_ bv113 32) (bvadd ((_ zero_extend 24) T) (bvmul (_ bv3 32) (bvadd ((_ zero_extend 31) T1) (bvmul (_ bv3 32) (bvadd ((_ zero_extend 24) T) (bvmul (_ bv113 32) (bvadd ((_ zero_extend 31) T1) (bvmul (_ bv113 32) (bvadd ((_ zero_extend 31) T1) (bvmul (_ bv3 32) (bvadd ((_ zero_extend 28) __) (bvmul (_ bv3 32) (bvadd (_ bv42476 32) (_ bv1 32))))))))) ((_ zero_extend 31) T1)))))))) (bvadd ((_ zero_extend 24) T1@) (bvmul (_ bv3 32) ((_ zero_extend 31) T1))))))
(check-sat)
