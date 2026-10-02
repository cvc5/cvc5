; REQUIRES: unrestricted-mode
; EXPECT: unsat
(set-logic ALL)
(declare-fun p () Real)
(declare-fun q () Real)
(assert (<= (sqrt (abs p)) (/ 7 10)))
(assert (<= (sqrt (abs q)) (/ 4 5)))
(assert (>= (+ (abs p) (* (/ 3 5) (abs q))) (/ 49 50)))
(check-sat)
