; COMMAND-LINE: --strings-exp
; EXPECT: unsat
(set-logic ALL)
(set-option :incremental false)
(declare-fun x () String)
(declare-fun y () String)
(assert (= x (str.++ "abcd" y)))
(assert (= (str.at x 0) (str.at x 2)))
(check-sat)
