; COMMAND-LINE: --fmf-fun-rlv --sygus-inference
; EXPECT: sat
(set-logic QF_NRA)
(declare-fun a () Real)
(assert (= (/ a a) 1.0))
(check-sat)
