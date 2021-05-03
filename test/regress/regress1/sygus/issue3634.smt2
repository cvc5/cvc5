; EXPECT: sat
; COMMAND-LINE: --sygus-inference -q
(set-logic ALL)
(declare-fun a () Int)
(declare-fun b () Real)
(assert (= (/ 1 (to_real a)) b))
(check-sat)
