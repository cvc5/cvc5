; COMMAND-LINE: --strings-exp
; EXPECT: sat
(set-logic QF_SLIA)
(set-info :status sat)
(declare-fun y () String)
(assert (str.< "AC" y))
(assert (str.< y "AF"))
(check-sat)
