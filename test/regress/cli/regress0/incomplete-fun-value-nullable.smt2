; COMMAND-LINE: --produce-models --default-function-value-mode=first-enum
; EXPECT: sat
; EXPECT: (
; EXPECT: (define-fun f ((_arg_1 Int)) (Nullable Int) (ite (= _arg_1 1) (nullable.some 1) (as nullable.null (Nullable Int))))
; EXPECT: )
(set-logic ALL)
(declare-fun f (Int) (Nullable Int))
(assert (= (f 1) (nullable.some 1)))
(assert (= (f 2) (as nullable.null (Nullable Int))))
(check-sat)
(get-model)
