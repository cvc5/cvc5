; COMMAND-LINE: --lang=smt2.6 --produce-models
; EXPECT: sat
; EXPECT: ((x "\u{a}"))
; EXPECT: ((y "\u{7f}"))
(set-logic ALL)
(set-info :status sat)
(declare-fun x () String)
(declare-fun y () String)
(assert (= (str.to_code x) 10))
(assert (= (str.to_code y) 127))
(check-sat)
(get-value (x))
(get-value (y))
