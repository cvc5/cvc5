; COMMAND-LINE: --check-models
; EXPECT: sat
(set-logic QF_FP)
(declare-const FP_VAR_a (_ FloatingPoint 11 53))
(declare-const FP_VAR_b (_ FloatingPoint 11 53))
(assert ( = (fp #b0 #b00000000000 #b0000000000000000000000000000000000000000000000000000)
(fp.div RTN (fp.fma RTP FP_VAR_a FP_VAR_a 
(fp #b0 #b00000000000 #b0000000000000000000000000000000000000000000000000000)) FP_VAR_b)))
(check-sat)
