; COMMAND-LINE: --bv-solver=bitblast-internal
; EXPECT: unsat
(set-logic ALL)
(declare-const __ (_ BitVec 7))
(assert (bvule ((_ zero_extend 31) ((_ zero_extend 16) ((_ zero_extend 8) __))) ((_ zero_extend 30) ((_ zero_extend 1) ((_ zero_extend 16) ((_ zero_extend 8) __))))))
(check-sat-assuming ((not (bvule (bvsub ((_ zero_extend 32) ((_ zero_extend 1) ((_ zero_extend 16) ((_ zero_extend 8) __)))) (_ bv1 64)) (bvsub ((_ zero_extend 1) ((_ zero_extend 1) ((_ zero_extend 31) ((_ zero_extend 16) ((_ zero_extend 8) __))))) (_ bv1 64))))))
