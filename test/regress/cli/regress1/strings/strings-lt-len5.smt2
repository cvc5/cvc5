; COMMAND-LINE: --strings-exp
; EXPECT: sat
(set-logic QF_SLIA)
(set-info :status sat)
(declare-fun y () String)
(assert (> (str.len y) 5))
(assert (str.< "ACAAB" y))
(assert (str.< y "ACAAD"))
(check-sat)
