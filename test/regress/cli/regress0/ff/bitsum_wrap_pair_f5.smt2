; REQUIRES: cocoa
; EXPECT: sat
; COMMAND-LINE: --ff-solver split
; COMMAND-LINE: --ff-solver gb
; Two 3-bit bitsums over F_5 can be equal mod 5 with different bits (1 = 6 mod 5).
(set-logic QF_FF)
(declare-const x (_ FiniteField 5))
(declare-const y (_ FiniteField 5))
(declare-const z (_ FiniteField 5))
(declare-const u (_ FiniteField 5))
(declare-const v (_ FiniteField 5))
(declare-const w (_ FiniteField 5))
(assert (= (ff.mul x x) x))
(assert (= (ff.mul y y) y))
(assert (= (ff.mul z z) z))
(assert (= (ff.mul u u) u))
(assert (= (ff.mul v v) v))
(assert (= (ff.mul w w) w))
(assert (= (ff.bitsum x y z) (ff.bitsum u v w)))
(assert (= x #f1m5))
(assert (= u #f0m5))
(check-sat)
