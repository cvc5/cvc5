; EXPECT: unsat
; EXPECT: unsat
(set-logic ALL)
(declare-const __ (_ BitVec 1))
(set-option :incremental true)
(check-sat-assuming ((bvsgt ((_ sign_extend 42) (bvcomp ((_ zero_extend 10) __) ((_ zero_extend 10) __))) (_ bv0 43))))
(check-sat-assuming ((bvsgt ((_ sign_extend 42) (bvcomp ((_ zero_extend 10) __) ((_ zero_extend 10) __))) (_ bv0 43))))