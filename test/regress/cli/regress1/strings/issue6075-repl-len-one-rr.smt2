; COMMAND-LINE: --strings-exp
; EXPECT: unsat
(set-logic ALL)
(declare-fun x () String)
(declare-fun y () String)
(assert (str.< x (str.replace "" (str.++ (str.replace "B" x "")
(str.replace "B" (str.replace "B" x "") "")) y)))
(check-sat)
