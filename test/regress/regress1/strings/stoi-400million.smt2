; COMMAND-LINE: --strings-exp
; EXPECT: sat
(set-info :smt-lib-version 2.6)
(set-logic ALL)
(declare-fun s () String)
(assert (> (str.to_int s) 400000000))
(check-sat)
