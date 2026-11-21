; REQUIRES: unrestricted-mode
; EXPECT: unknown
(set-logic ALL)
(declare-const x Real)
(assert (= (arccsc (- 1.0)) (- (/ real.pi 2.0))))
(check-sat)
