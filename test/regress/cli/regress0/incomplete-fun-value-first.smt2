; COMMAND-LINE: --produce-models --default-function-value-mode=first
; EXPECT: sat
; EXPECT: (
; EXPECT: (define-fun f ((_arg_1 Int)) Int 1)
; EXPECT: )
(set-logic ALL)
(declare-fun f (Int) Int)
(assert (= (f 1) 1))
(check-sat)
(get-model)
