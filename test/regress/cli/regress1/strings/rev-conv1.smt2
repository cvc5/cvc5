; COMMAND-LINE: --strings-exp
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(declare-fun x () String)
(assert (= (str.rev (str.to_upper x)) "CBA"))
(assert (not (= x "ABC")))
(assert (not (= x "abc")))
(check-sat)
