; EXPECT: sat
; COMMAND-LINE: --sygus-inference
(set-logic ALL)
(set-option :miniscope-quant agg)
(set-option :sygus-inference true)
(declare-fun a () Real)
(declare-fun b () Real)
(assert (forall ((c Real)) (or (< c a) (< 0.0 b))))
(check-sat)
