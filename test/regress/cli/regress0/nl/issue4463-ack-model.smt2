; EXPECT: sat
(set-logic QF_NIA)
(set-option :ackermann true)
(assert (= (mod 75 0) 683))
(check-sat)
