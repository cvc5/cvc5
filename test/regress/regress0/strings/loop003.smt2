(set-logic QF_S)
(set-info :status sat)

(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () String)
(declare-fun w () String)
(declare-fun w1 () String)
(declare-fun w2 () String)

(assert (= (str.++ x "aaaae") (str.++ "eaaaa" x)))

(check-sat)
