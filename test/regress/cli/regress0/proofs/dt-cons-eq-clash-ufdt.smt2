; EXPECT: unsat
; Minimal UFDT example (in the spirit of SMT-LIB cdt-cade2015) that exercises
; dt-cons-eq-clash where the constructor clash (a vs b in the right child) is
; only reached after recursing past a non-constructor sibling argument (the
; uninterpreted-function application (f x) in the left child). The
; $dt_distinct_terms side condition must return false for the non-constructor
; sibling rather than aborting, while still finding the clash.
(set-logic UFDT)
(declare-datatype D ((c (left D) (right D)) (a) (b)))
(declare-fun f (D) D)
(declare-const x D)
(assert (= (c (f x) a) (c a b)))
(check-sat)
