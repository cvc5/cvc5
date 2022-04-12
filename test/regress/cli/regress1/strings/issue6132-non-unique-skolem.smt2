; COMMAND-LINE: --strings-exp
; EXPECT: sat
(set-logic ALL)
(declare-fun str () String)                                                        
(assert (= 0 (ite (= str (str.from_code 
             (ite (= 0 (ite (> (str.len (str.from_int (str.len str))) 1) 1 0)) 1 0))) 1 0)))
(check-sat)
