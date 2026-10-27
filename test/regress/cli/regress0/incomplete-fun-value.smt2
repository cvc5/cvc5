; COMMAND-LINE: --produce-models --default-function-value-mode=hole
; EXPECT: sat
; EXPECT: (
; EXPECT: (define-fun f ((_arg_1 Int)) Int (ite (= _arg_1 0) 1 @ground_term_2))
; EXPECT: )
(set-logic ALL)
(declare-fun f (Int) Int)
(assert (= (f 0) 1))
(check-sat)
(get-model)
