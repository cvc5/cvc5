; COMMAND-LINE: --produce-models
; EXPECT: sat
; EXPECT: (
; EXPECT: (define-fun f ((_arg_1 Int)) Int 0)
; EXPECT: )
(set-logic ALL)
(set-option :incremental false)
(declare-fun f (Int) Int)
(assert (= (f 1) 0))
(check-sat)
(get-model)
