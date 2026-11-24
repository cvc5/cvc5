; EXPECT: sat
(set-logic ALL)
(set-info :a)
(set-info :ab)
(declare-const a Bool)
(assert (! a :named b))
(check-sat)
