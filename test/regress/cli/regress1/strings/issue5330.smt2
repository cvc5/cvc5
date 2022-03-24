; COMMAND-LINE: --strings-exp
; EXPECT: sat
(set-logic QF_SLIA)
(declare-fun str1 () String)
(declare-fun str18 () String)
(assert (str.in_re (str.replace str18 str1 str18) (str.to_re "pANjvthXNyBbIgIlkC")))
(check-sat)
