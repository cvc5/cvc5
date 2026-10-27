; REQUIRES: cocoa
; EXPECT: sat
; COMMAND-LINE: --ff-solver split
; COMMAND-LINE: --ff-solver gb
(set-info :smt-lib-version 2.6)
(set-info :category "crafted")
(set-logic QF_FF)
(define-sort F2 () (_ FiniteField 2))
(assert (= (as ff-9 F2) (ff.bitsum (as ff-9 F2) (as ff-10 F2))))
(check-sat)
