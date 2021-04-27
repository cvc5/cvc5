; COMMAND-LINE:
; EXPECT: sat
(set-logic NRA)
(set-info :status sat)
(declare-fun a () Real)
(declare-fun b () Real)
(assert (= (* a b) 1))
(check-sat)
