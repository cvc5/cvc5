; COMMAND-LINE: --hol
; EXPECT: sat
(set-logic QF_AUFBVLIA)
(declare-fun a (Int) Int)
(declare-fun b (Int) Int)
(assert (distinct a b))
(check-sat)
