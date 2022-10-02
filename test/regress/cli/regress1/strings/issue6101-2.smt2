; COMMAND-LINE: --strings-exp
; EXPECT: unsat
(set-logic ALL)
(declare-fun x () String)
(assert (not (= x (str.replace x (str.replace "B" (str.replace x (str.replace x "A" "B") "B") "B") "B"))))
(check-sat)
