; COMMAND-LINE: --strings-exp
; EXPECT: unsat
(set-logic ALL)
(set-info :status unsat)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () Int)
(assert (= (str.replace (str.replace x "B" (str.++ "B" "B")) "B" (str.++ y "B")) (str.++ y "B")))
(check-sat)
