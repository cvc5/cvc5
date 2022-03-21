; COMMAND-LINE: --produce-abducts
; EXPECT: none
(set-logic ALL)
(assert (= 0.0 (sqrt 1.0)))
(get-abduct A false)
