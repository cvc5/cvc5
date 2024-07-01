; EXPECT: sat
(set-logic ALL)
(set-option :fmf-bound true)
(set-option :global-negate true)
(declare-datatypes ((d 0)) (((c (s Bool)))))
(declare-const x d)
(assert (s x))
(check-sat)
