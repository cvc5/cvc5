; COMMAND-LINE: --strings-exp
; EXPECT: unsat
(set-logic ALL)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () Int)
(assert (= (= x (str.replace x (str.replace "B" (str.replace x (str.replace x "A" "B") "B") "B") "B")) (not (= 
(not (not (= (= "A" (str.replace x "A" "B")) false))) (not (not (= (= "A" (str.replace x "A" "B")) false)))))))
(check-sat)
