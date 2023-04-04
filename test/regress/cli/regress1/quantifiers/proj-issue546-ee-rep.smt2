; EXPECT: sat
(set-logic ALL)
(set-option :quant-rep-mode ee)
(declare-const x String)
(assert (str.is_digit (str.rev x)))
(check-sat)
