; EXPECT: sat
(set-logic ALL)
(set-option :global-negate true)
(assert true)
(check-sat)
