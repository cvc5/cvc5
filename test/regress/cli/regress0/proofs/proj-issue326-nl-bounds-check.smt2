; COMMAND-LINE: -q
; EXPECT: sat
(set-logic ALL)
(set-option :check-proofs true)
(set-option :proof-check eager)
(declare-const x Real)
(assert
    (and
        (< 1.0 x)
        (<= x (/ 0.0 0.0 x))
        (<= (/ 0.0 0.0 x) x)
    )
)
(check-sat)
