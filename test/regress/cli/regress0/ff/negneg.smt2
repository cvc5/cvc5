; REQUIRES: cocoa
; EXPECT: unsat
; x, m, is_zero: field
; The constraints mx - 1 + is_zero = 0
;                 is_zero*x = 0
; Imply that is_zero is zero or one and = (x == 0)
(set-info :smt-lib-version 2.6)
(set-info :category "crafted")
(set-logic QF_FF)
(define-sort F () (_ FiniteField 17))
(declare-fun x () F)
(assert (not (= (ff.neg (ff.neg x)) x)))
(check-sat)
