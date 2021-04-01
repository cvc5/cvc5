; COMMAND-LINE: --strings-exp
; EXPECTED: unsat
(set-logic ALL)
(declare-fun x () String)
(declare-fun y () String)
(assert (= (= (str.suffixof "B" (str.replace (str.replace "A" (str.replace x "B" "A") "") "A" "")) 
(str.suffixof "B" (str.replace x "B" "A"))) (str.suffixof "B" (str.replace x "B" "A"))))
(check-sat)
(exit)
