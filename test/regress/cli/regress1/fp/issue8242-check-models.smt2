; COMMAND-LINE: --check-models
; EXPECT: sat
(set-logic QF_FP)
(declare-const a (_ FloatingPoint 11 53))
(declare-const b (_ FloatingPoint 11 53))
(assert
  (fp.leq
    (fp.sub RTZ
            b
            (fp #b0
                #b00000000000
                #b0000000000000000000000000000000000000000000000000000))
    (fp.div RTN b a)))
(check-sat)
