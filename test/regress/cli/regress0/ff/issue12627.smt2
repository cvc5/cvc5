; REQUIRES: cocoa
; EXPECT: sat
; COMMAND-LINE: --ff-solver split
; COMMAND-LINE: --ff-solver gb
(set-logic QF_FF)
(declare-const a (_ FiniteField 3))
(declare-const b (_ FiniteField 3))
(assert (= (ff.mul a b) (ff.mul b a)))
(check-sat)
