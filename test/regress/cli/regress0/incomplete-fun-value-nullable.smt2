; COMMAND-LINE: --produce-models --default-function-value-mode=first-enum
; EXPECT: sat
; EXPECT: (
; EXPECT: (define-fun f ((_arg_1 Int)) Int (ite (= _arg_1 0) (nullable.some 1) (as nullable.null (Nullable Int))))
; EXPECT: )
(set-logic ALL)
(declare-fun f (Int) (Nullable Int))
(assert (= (f 0) (nullable.some 1)))
(check-sat)
(get-model)
