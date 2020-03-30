; COMMAND-LINE: --produce-interpols
; EXIT: 0
(set-logic NIA)
(declare-fun x ( ) Int)
(declare-fun y ( ) Int)
(declare-fun z ( ) Int)
(assert (= (* 2 x) y))
(get-interpol A (distinct (+ (* 2 z) 1) y))
