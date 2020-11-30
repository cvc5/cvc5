; COMMAND-LINE: --produce-models --lang=smt2.6
; EXPECT: sat
; EXPECT: ((x "\u{5c}u1000"))
(set-logic ALL)
(set-info :status sat)
(declare-const x String)
(assert (= x (str.++ "\u" "1000")))
(check-sat)
(get-value (x))
