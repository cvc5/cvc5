; COMMAND-LINE: --check-models
; EXPECT: sat
(set-logic QF_FP)
(declare-const a (_ FloatingPoint 11 53))
(declare-const b (_ FloatingPoint 11 53))
(assert (= b (fp.div RTZ b (fp.div RTZ a b))))
(check-sat)
