; COMMAND-LINE: --arith-rewrite-equalities --global-negate --no-check-models
; EXPECT: sat
(set-logic NIA)
(set-option :arith-rewrite-equalities true)
(set-option :global-negate true)
(set-info :status sat)
(declare-const i5 Int)
(assert (= 562 (abs i5)))
(check-sat)
