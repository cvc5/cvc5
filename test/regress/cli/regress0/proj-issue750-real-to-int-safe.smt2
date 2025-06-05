; EXPECT: sat
(set-option :check-proofs true)
(set-logic ALL)
(set-option :solve-real-as-int true)
(declare-const x Real)
(assert (= 0.0 x))
(check-sat)
