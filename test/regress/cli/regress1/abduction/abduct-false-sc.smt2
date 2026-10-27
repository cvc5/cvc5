; COMMAND-LINE: --produce-abducts
; EXPECT: fail
(set-logic ALL)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (and (> x 5) (< x 2)))
(get-abduct A (> x y))
