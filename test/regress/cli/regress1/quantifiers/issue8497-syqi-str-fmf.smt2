; COMMAND-LINE: --sygus-inst
; EXPECT: sat
(set-logic QF_SLIA)
(declare-fun a () String)
(declare-fun b () String)
(assert (> (str.indexof a b 0) 2))
(check-sat)
