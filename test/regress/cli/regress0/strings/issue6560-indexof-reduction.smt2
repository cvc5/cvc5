; COMMAND-LINE: --strings-exp
; EXPECT: unsat
(set-logic ALL)
(set-info :status unsat)
(declare-fun a () String)
(assert (> (str.indexof a "" (* 2 (str.len a))) 0))
(check-sat)
