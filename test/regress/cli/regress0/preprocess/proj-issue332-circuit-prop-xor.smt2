; EXPECT: sat
(set-logic ALL)
(set-option :produce-proofs true)
(declare-const x Real)
(declare-const x4 Real)
(declare-const x8 Bool)
(assert (<= x4 x))
(assert (not (xor (> x4 x) x8)))
(check-sat)
