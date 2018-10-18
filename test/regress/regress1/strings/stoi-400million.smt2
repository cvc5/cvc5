; COMMAND-LINE: --strings-exp
; EXPECT: sat
(set-info :smt-lib-version 2.5)
(set-logic ALL)
(declare-fun s () String)
(assert (> (str.to.int s) 400000000))
(check-sat)
