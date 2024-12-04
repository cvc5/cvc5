; EXPECT: sat
(set-logic ALL)
(declare-const a Bool)
(declare-const b Bool)
(assert b)
(assert (xor b (not a)))
(check-sat)
