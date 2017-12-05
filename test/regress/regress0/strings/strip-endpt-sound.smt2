; COMMAND-LINE: --strings-exp
; EXPECT: sat
(set-logic QF_S)
(declare-fun x () String)
(declare-fun y () String)

(assert (str.contains "c(ab)" (str.++ x ")")))
(assert (str.contains "c(ab)" (str.++ "c(" y)))

(declare-fun z () String)
(declare-fun w () String)

(assert (str.contains "c(ab))" (str.++ z "))")))
(assert (str.contains z "b"))

(assert (str.contains "c(ab))" (str.++ w "b)")))
(assert (str.contains w "a"))


(declare-fun p () String)
(declare-fun q () String)

(assert (str.contains "c(aab))" (str.++ "a" p)))
(assert (str.contains p "a"))

(assert (str.contains "c(abb))" (str.++ q "b")))
(assert (str.contains q "b"))

(check-sat)
