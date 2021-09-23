; COMMAND-LINE: --strings-exp
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(declare-fun str0 () String)
(declare-fun str3 () String)
(declare-fun str8 () String)
(assert (str.< str8 str3))
(assert (str.prefixof (str.++ str8 (str.++ str0 (str.++ "K" str8))) (str.++ (str.++ str0 str8) (str.++ str0 str3 "Q"))))
(check-sat)
