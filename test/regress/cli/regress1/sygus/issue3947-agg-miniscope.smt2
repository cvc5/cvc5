; EXPECT: sat
; COMMAND-LINE: --sygus-inference=try
(set-logic ALL)
(set-option :miniscope-quant agg)
(set-option :sygus-inference try)
(declare-fun a () Real)
(declare-fun b () Real)
(assert (forall ((c Real)) (or (< c a) (< 0.0 b))))
(check-sat)
