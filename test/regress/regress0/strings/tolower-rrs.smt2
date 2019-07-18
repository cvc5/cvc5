; COMMAND-LINE: --strings-exp
; EXPECT: unsat
(set-logic ALL)
(set-info :status unsat)
(declare-fun x () String)

(assert (or 
(not (= (str.tolower (str.toupper (str.tolower x))) (str.tolower x)))
(not (= (str.tolower (str.++ x "A")) (str.++ (str.tolower x) "a")))
))

(check-sat)
