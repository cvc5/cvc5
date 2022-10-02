; COMMAND-LINE: --strings-exp
; EXPECT: sat
(set-logic ALL)
(declare-fun a () String)
(declare-fun e () String)
(declare-fun v () String)
(assert (exists ((E String)) (and (distinct v e) (distinct e a) (distinct v "A") (> (str.to_code a) 65))))
(check-sat)
