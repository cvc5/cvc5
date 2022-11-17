; COMMAND-LINE: --produce-interpolants
; EXPECT: (define-fun A () Bool false)
(set-logic ALL)
(declare-fun a () Int)
(assert (<= 1 0))
(get-interpolant A (> a 0))
