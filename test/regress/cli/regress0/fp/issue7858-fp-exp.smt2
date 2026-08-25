; COMMAND-LINE: --fp-exp
; EXPECT: sat
(set-logic QF_FP)
(declare-fun v () Float64)
(assert (= ((_ to_fp 9 53) RNE v) (fp (_ bv0 1) (_ bv0 9) (_ bv0 52))))
(check-sat)
