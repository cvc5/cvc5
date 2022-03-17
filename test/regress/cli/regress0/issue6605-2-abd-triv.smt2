; COMMAND-LINE: --produce-abducts
; EXPECT: (define-fun A () Bool true)
(set-logic ALL)
(get-abduct A true)
