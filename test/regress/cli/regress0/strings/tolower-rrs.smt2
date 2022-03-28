; COMMAND-LINE: --strings-exp
; EXPECT: unsat
(set-info :smt-lib-version 2.6)
(set-logic ALL)
(set-info :status unsat)
(declare-fun x () String)
(declare-fun y () Int)

(assert (or 
(not (= (str.to_lower (str.to_upper (str.to_lower x))) (str.to_lower x)))
(not (= (str.to_lower (str.++ x "A")) (str.++ (str.to_lower x) "a")))
(not (= (str.to_lower (str.from_int y)) (str.from_int y)))
))

(check-sat)
