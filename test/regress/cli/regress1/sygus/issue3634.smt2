; EXPECT: sat
; COMMAND-LINE: --sygus-inference
(set-logic ALL)
(declare-fun a () Int)
(declare-fun b () Real)
(assert (= (/ 1.0 (to_real a)) b))
(check-sat)
