; COMMAND-LINE: --strings-exp -q
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(declare-fun w () String)
(declare-fun q () String)
(assert (= (str.len q) 99999999999999999999999999999999999999))
(assert (= w (str.++ q "A")))
(check-sat)
