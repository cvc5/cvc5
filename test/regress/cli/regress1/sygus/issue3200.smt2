; EXPECT: sat
; COMMAND-LINE: --sygus-inference=try
(set-logic ALL)
(declare-fun v () Real)
(assert (= (* v v) 0.0))
(check-sat)
(exit)
