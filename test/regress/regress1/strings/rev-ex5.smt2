; COMMAND-LINE: --strings-exp
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(declare-fun x () String)
(assert (= x (str.rev x)))
(assert (> (str.len x) 1))
(check-sat)
