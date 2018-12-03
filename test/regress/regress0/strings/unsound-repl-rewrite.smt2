; COMMAND-LINE: --strings-exp
; EXPECT: sat
(set-logic QF_S)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () Int)
(assert (not (= (str.replace "B" (str.replace "" x "A") "B") (str.replace "B" x "B"))))
(check-sat)
