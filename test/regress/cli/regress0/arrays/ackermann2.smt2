; COMMAND-LINE: --ackermann
; EXPECT: sat
(set-logic QF_ALIA)
(declare-const a (Array Int Int))
(declare-const b (Array Int Bool))
(assert (> (select a 0) 5))
(assert (select b 0))
(check-sat)
