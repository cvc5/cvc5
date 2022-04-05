; COMMAND-LINE: --strings-exp -q
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(declare-fun str9 () String)
(declare-fun i3 () Int)
(assert (= 0 (- (str.indexof str9 (str.substr str9 1 1) i3) (- (* 137 (- (* 74 74 25 25 12)))))))
(check-sat)
