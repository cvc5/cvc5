; REQUIRES: poly
; EXPECT: sat
(set-info :smt-lib-version 2.6)
(set-logic QF_NRA)
(set-info :status sat)
(declare-fun skoS3 () Real)
(declare-fun skoSX () Real)
(declare-fun skoX () Real)
(assert (and 
(not (= (* skoX (* skoX (- 80))) (+ 75 (* skoSX (* skoSX (- 1)))))) 
(= (* skoS3 skoS3) 3) 
(not (<= skoX 0)) 
(not (<= skoSX 0)) 
(not (<= skoS3 0))
))
; cannot construct an exact model, but can reason that this is SAT based on approximation
(check-sat)
