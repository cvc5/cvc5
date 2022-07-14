; COMMAND-LINE: --strings-exp --no-strings-lazy-pp
; EXPECT: unsat
(set-logic ALL)
(declare-fun a () String)
(assert (<= (str.to_int (str.++ "0" (str.from_int (ite (str.prefixof "-" (str.at a 2)) 0 (str.to_int (str.at a 2)))))) (- 1)))
(check-sat)
