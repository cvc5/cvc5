; COMMAND-LINE: --deep-restart=input
; EXPECT: sat
(set-logic QF_SLIA)
(declare-const x Bool)
(declare-fun s () String)
(assert (not (<= 0 (ite x 0 (str.to_int (str.substr s 0 1))))))
(check-sat)
