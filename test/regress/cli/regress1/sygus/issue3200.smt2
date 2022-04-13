; EXPECT: sat
; COMMAND-LINE: --sygus-inference
(set-logic ALL)
(declare-fun v () Real)
(assert (= (* v v) 0.0))
(check-sat)
(exit)
