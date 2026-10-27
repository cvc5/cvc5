; COMMAND-LINE: --decision=internal
; EXPECT: unsat
(set-logic ALL)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () Int)
(assert (distinct (str.substr x 1 (str.indexof "B" y z)) (str.substr x 1 (str.indexof "A" y z))))
(check-sat)
