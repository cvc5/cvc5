; COMMAND-LINE: --ackermann
; EXPECT: sat
(set-logic QF_ALIA)
(declare-const a (Array Int Int))
(declare-const b (Array Bool Int))
(assert (= (select a 0) 5))
(assert (= (select b true) 10))
(check-sat)
