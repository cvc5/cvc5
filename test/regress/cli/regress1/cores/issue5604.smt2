; COMMAND-LINE: --strings-exp
; EXPECT: unsat
(set-logic ALL)
(declare-fun a () String)
(declare-fun b () String)
(declare-fun c () String)
(assert (xor (str.prefixof (str.replace "B" (str.substr a 0 (str.len b)) "") b) (str.prefixof "B" b)))
(assert (= a (str.++ b c)))
(check-sat)
