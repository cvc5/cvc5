; REQUIRES: cocoa
; EXPECT: sat
; COMMAND-LINE: --ff-solver split
; COMMAND-LINE: --ff-solver gb
; x, y are bits; x = y = 1 gives bitsum(x, y, y) = 1 + 2 + 4 = 7 = 0 (mod 7).
(set-logic QF_FF)
(declare-const x (_ FiniteField 7))
(declare-const y (_ FiniteField 7))
(assert (= (ff.mul x x) x))
(assert (= (ff.mul y y) y))
(assert (= x #f1m7))
(assert (= #f0m7 (ff.bitsum x y y)))
(check-sat)
