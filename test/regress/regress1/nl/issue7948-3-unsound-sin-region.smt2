; COMMAND-LINE: --simplification=none
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(declare-fun a () Real)
(declare-fun b () Real)
(assert (and (= a 0) (= b (cos a))))
(check-sat)
