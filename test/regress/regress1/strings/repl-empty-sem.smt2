; COMMAND-LINE: --strings-exp
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(declare-fun x () String)
(declare-fun z () String)
(assert (= (str.len z) 0))
(assert (= (str.replace "ab" z "c") x))
(declare-fun y () String)
(assert (= x (str.++ "c" y)))
(check-sat)
