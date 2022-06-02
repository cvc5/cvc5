; COMMAND-LINE: --produce-interpolants -q
; EXPECT: fail
(set-logic ALL)
(declare-fun a () Int)
(get-interpolant A (> a 0))
