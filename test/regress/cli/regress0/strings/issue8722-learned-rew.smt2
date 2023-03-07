; COMMAND-LINE: --learned-rewrite --strings-exp
; EXPECT: sat
(set-logic ALL)
(declare-const a String) 
(assert (str.is_digit a)) 
(check-sat)
