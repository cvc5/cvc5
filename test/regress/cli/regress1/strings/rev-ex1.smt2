; COMMAND-LINE: --strings-exp
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () String)
(assert (not (= (str.rev (str.++ x y)) (str.rev (str.++ x z)))))
(check-sat)
