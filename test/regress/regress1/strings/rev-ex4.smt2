; COMMAND-LINE: --strings-exp --strings-fmf
; EXPECT: unsat
(set-logic ALL)
(set-info :status unsat)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () String)
(declare-fun w () String)
(assert (= x (str.rev y)))
(assert (= y (str.rev z)))
(assert (distinct x z w))
(assert (< (str.len x) 2))
(check-sat)
