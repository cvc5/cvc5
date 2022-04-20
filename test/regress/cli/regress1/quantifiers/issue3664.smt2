; COMMAND-LINE: --fmf-fun-rlv --sygus-inference
; EXPECT: sat
; DISABLE-TESTER: model
(set-logic QF_NRA)
(declare-fun a () Real)
(assert (= (/ a a) 1.0))
(check-sat)
