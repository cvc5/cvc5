; COMMAND-LINE: --unconstrained-simp --no-check-models
; EXPECT: sat
(set-logic QF_AUFBVLIA)
(declare-fun a () Int)
(declare-fun b (Int) Int)
(assert (distinct (b a) (b (b a))))
(check-sat)
