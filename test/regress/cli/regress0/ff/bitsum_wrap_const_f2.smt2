; REQUIRES: cocoa
; EXPECT: sat
; COMMAND-LINE: --ff-solver split
; COMMAND-LINE: --ff-solver gb
; Over F_2, bitsum(x, x) = 3x = x, so x = 1 is a solution.
(set-logic QF_FF)
(declare-const x (_ FiniteField 2))
(assert (= #f1m2 (ff.bitsum x x)))
(check-sat)
