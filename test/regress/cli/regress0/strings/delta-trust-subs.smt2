; COMMAND-LINE: --strings-exp
; EXPECT: unsat
(set-logic ALL)
(set-info :status unsat)
(declare-fun a () String)
(assert (= (str.++ a "0" (str.++ a a) "A") (str.++ "0" (str.from_code (str.len a)) (str.replace "A" (str.++ a "A") a))))
(check-sat)
