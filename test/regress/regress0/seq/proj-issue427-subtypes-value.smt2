; EXPECT: sat
; EXPECT: (((seq.unit _x0) (seq.unit 0.0)))
(set-logic ALL)
(set-option :global-declarations true)
(set-option :produce-models true)
(declare-const _x0 Real)
(assert (= _x0 0.0))
(check-sat)
(get-value ((seq.unit _x0)))
