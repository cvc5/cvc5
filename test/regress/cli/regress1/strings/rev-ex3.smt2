; COMMAND-LINE: --strings-exp
; EXPECT: unsat
(set-logic ALL)
(set-info :status unsat)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () String)
(declare-fun w () String)
(assert (= x (str.rev (str.++ y "A"))))
(assert (= x (str.rev (str.++ "B" z))))
(assert (= z (str.++ w "C")))
(check-sat)
