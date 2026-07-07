; COMMAND-LINE: --check-models
; EXPECT: sat
(set-logic QF_FP)
(declare-const a (_ FloatingPoint 11 53))
(declare-const b (_ FloatingPoint 11 53))
(assert (fp.eq (fp.sub RTN b b) (fp.div RNA a b)))
(check-sat)
