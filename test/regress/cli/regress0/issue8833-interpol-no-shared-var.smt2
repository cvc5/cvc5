; COMMAND-LINE: --produce-interpolants
; EXPECT: fail
(set-logic ALL)
(declare-fun a () Int)
(get-interpolant A (> a 0))
