; COMMAND-LINE: --learned-rewrite
; EXPECT: sat
(set-logic ALL)
(declare-const a String) 
(assert (str.is_digit a)) 
(check-sat)
