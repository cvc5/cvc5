; EXPECT: sat
; COMMAND-LINE: --sygus-inference
(set-logic ALL)
(declare-fun x () Real)
(assert (= x 1))
(assert (= (sqrt x) x))
(check-sat)
