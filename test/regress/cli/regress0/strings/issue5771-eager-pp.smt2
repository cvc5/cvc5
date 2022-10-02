; COMMAND-LINE: --no-strings-lazy-pp --strings-exp
; EXPECT: sat
(set-logic ALL)
(declare-fun a () Int)
(assert (str.suffixof "B" (str.from_code a)))
(check-sat)
