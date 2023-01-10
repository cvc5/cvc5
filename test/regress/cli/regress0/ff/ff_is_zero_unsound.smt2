; REQUIRES: cocoa
; EXPECT: sat
; COMMAND-LINE: --no-debug-check-models
; x, m, is_zero: field
; The constraints mx - 1 + is_zero = 0
;                 is_zero*m = 0                     ;; Note: this *should* be is_zero*x=0
; Imply that is_zero is zero or one and = (x == 0)
(set-info :smt-lib-version 2.6)
(set-info :category "crafted")
(set-logic QF_FF)
(declare-fun x () (_ FiniteField 17))
(declare-fun m () (_ FiniteField 17))
(declare-fun is_zero () (_ FiniteField 17))
(assert (not (=>
  (and (= #f0m17 (ff.add (ff.mul m x) #f16m17 is_zero))
       (= #f0m17 (ff.mul is_zero m)))
  (and (or (= #f0m17 is_zero) (= #f1m17 is_zero))
       (= (= #f1m17 is_zero) (= x #f0m17)))
)))
(check-sat)
