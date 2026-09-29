; EXPECT: unsat
; Minimal QF_DT example (reduced from SMT-LIB barrett-jsat v1l20018) that
; exercises dt-cons-eq-clash where the constructor clash (null vs cons in the
; cdr) is only reached after recursing past a non-constructor sibling argument
; (the selector application (car x2) in the car). The $dt_distinct_terms side
; condition must return false for the non-constructor sibling rather than
; aborting, while still finding the clash.
(set-logic QF_DT)
(declare-datatypes ((nat 0)(list 0)(tree 0)) (
  ((succ (pred nat)) (zero))
  ((cons (car tree) (cdr list)) (null))
  ((node (children list)) (leaf (data nat)))))
(declare-fun x2 () list)
(declare-fun x3 () tree)
(assert (= (cons (car x2) null) (cons x3 (cons x3 (children (car null))))))
(check-sat)
