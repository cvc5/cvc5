; EXPECT: sat
; COMMAND-LINE: --sygus-inference
(set-logic QF_LRA)
(declare-fun v () Real)
(assert (= v 0))
(check-sat)
(exit)
