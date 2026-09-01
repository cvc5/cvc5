; REQUIRES: unrestricted-mode
; COMMAND-LINE: --check-models
; EXPECT: sat
;; The zero case of fp.min/fp.max is unspecified. Check that the value the
;; model assigns to it agrees with the way FLOATINGPOINT_{MIN,MAX}_TOTAL is
;; bit-blasted, for both operand orders and both literal back ends.
(set-logic QF_FP)
(assert (fp.isNegative (fp.max (_ +zero 8 24) (_ -zero 8 24))))
(assert (fp.isPositive (fp.max (_ -zero 8 24) (_ +zero 8 24))))
(assert (fp.isPositive (fp.min (_ +zero 8 24) (_ -zero 8 24))))
(assert (fp.isNegative (fp.min (_ -zero 8 24) (_ +zero 8 24))))
(check-sat)
