; COMMAND-LINE: --produce-models --model-print-partial-fun
; EXPECT: sat
; EXPECT: (
; EXPECT: (refine-fun / ((_arg_1 Real) (_arg_denominator_2 Real)) Real (ite (= _arg_denominator_2 0.0) 7.0 (/ _arg_1 _arg_denominator_2)))
; EXPECT: )
(set-logic ALL)
(assert (= (/ 0.0 0.0) 7.0))
(check-sat)
(get-model)
