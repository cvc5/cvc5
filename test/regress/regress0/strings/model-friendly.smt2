; COMMAND-LINE: --lang=smt2.6.1 --produce-models
; EXPECT: sat
; EXPECT: ((x "AAAAA"))
(set-logic ALL)
(set-info :status sat)
(declare-fun x () String)
(assert (= (str.len x) 5))
(check-sat)
(get-value (x))
