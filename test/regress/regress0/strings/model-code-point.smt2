; COMMAND-LINE: --lang=smt2.6.1 --produce-models
; EXPECT: sat
; EXPECT: ((x "\u{A}"))
(set-logic ALL)
(set-info :status sat)
(declare-fun x () String)
(assert (= (str.code x) 10))
(check-sat)
(get-value (x))
