; COMMAND-LINE: --strings-exp
; EXPECT: sat
(set-logic ALL)
(declare-fun x () String)
(declare-fun y () String)
(assert (= (str.++ "A" y) (str.replace x (str.++ "A" y) (str.replace (str.++ "A" (str.replace y "" "A")) x "A"))))
(check-sat)
