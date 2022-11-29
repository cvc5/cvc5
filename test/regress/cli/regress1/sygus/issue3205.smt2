; EXPECT: sat
; COMMAND-LINE: --sygus-inference
(set-logic ALL)
(declare-fun a () Real) 
(assert (= (* a a) 1.0))
(check-sat)
(exit)
