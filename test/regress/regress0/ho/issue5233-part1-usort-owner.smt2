; COMMAND-LINE: --uf-ho
; EXPECT: sat
(set-logic QF_AUFBVLIA)
(set-option :uf-ho true)
(declare-fun a (Int) Int)
(declare-fun b (Int) Int)
(assert (distinct a b))
(check-sat)
