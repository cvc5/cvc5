; Some test for the bitsum rewriter
; REQUIRES: cocoa
; EXPECT: sat
; COMMAND-LINE: --ff-solver split
; COMMAND-LINE: --ff-solver gb
(set-logic QF_FF)
(set-info :smt-lib-version 2.6)
(set-info :category "crafted")
(assert (= (ff.bitsum #f0m3 #f0m3 #f0m3) #f0m3))
(assert (= (ff.bitsum #f1m3 #f0m3 #f0m3) #f1m3))
(assert (= (ff.bitsum #f0m3 #f1m3 #f0m3) #f2m3))
(assert (= (ff.bitsum #f0m3 #f0m3 #f1m3) #f1m3))
(assert (= (ff.bitsum #f0m3 #f1m3 #f1m3) #f0m3))
(assert (= (ff.bitsum #f1m3 #f2m3 #f0m3) #f2m3))
(check-sat)

