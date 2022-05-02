; COMMAND-LINE: --strings-exp
; EXPECT: sat
(set-logic ALL)
(declare-fun a () String)
(declare-fun b () String)
(assert (= b (str.replace_re a (str.to_re "A") "A")))
(assert (not (str.prefixof (str.++ b b) a)))
(check-sat)
