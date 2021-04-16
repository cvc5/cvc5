; COMMAND-LINE: --finite-model-find
; EXPECT: sat
(set-logic AUFNIA)
(declare-sort S0 0)
(declare-const a (Array Int S0))
(declare-const b (Array Int S0))
(assert (distinct b a))
(check-sat)
