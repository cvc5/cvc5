; REQUIRES: unrestricted-mode
; EXPECT: unsat
(set-option :fp-exp true)
(set-logic ALL)
(assert (= #b1 (bvredor ((_ fp.to_sbv 1) roundTowardNegative (fp (_ bv0 1) (_ bv0 15) (_ bv0 112))))))
(check-sat)
