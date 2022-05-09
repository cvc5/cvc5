; COMMAND-LINE: --strings-exp
; EXPECT: unsat
(set-logic ALL)
(declare-fun x () String)
(declare-fun y () String)
(assert (distinct (str.replace (str.replace "B" x y) "A" x) (str.replace "B" x (str.replace y "A" x))))
(check-sat)
