; COMMAND-LINE: -q
; EXPECT: sat
(set-logic ALL)
(declare-fun x () Real)
(assert (< x 0.0))
(assert (not (= (/ (sqrt x) (sqrt x)) x)))
(set-info :status sat)
(check-sat)
