; COMMAND-LINE: --strings-exp
; EXPECT: unsat
(set-logic ALL)
(set-info :status unsat)
(declare-fun x () String)
(declare-fun y () String)
(assert (and
(= (str.replace x x "abc") "")
(= (str.replace (str.++ x y) x "abc") (str.++ x y))
(= (str.replace (str.++ x y) (str.substr x 0 2) "abc") y)
))
(check-sat)
