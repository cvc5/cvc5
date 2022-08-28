; COMMAND-LINE: --simplification=none -q
; EXPECT: sat
(set-logic ALL)
(declare-fun a () Real)
(declare-fun b () Real)
(assert (and (= a 0.0) (= b (cos a))))
(check-sat)
