; COMMAND-LINE: --strings-exp
; EXPECT: unsat
(set-info :smt-lib-version 2.6)
(set-logic ALL)
(set-info :status unsat)
(declare-fun x () String)
(declare-fun y () Int)

(assert (or 
(not (= (str.tolower (str.toupper (str.tolower x))) (str.tolower x)))
(not (= (str.tolower (str.++ x "A")) (str.++ (str.tolower x) "a")))
(not (= (str.tolower (str.from_int y)) (str.from_int y)))
))

(check-sat)
