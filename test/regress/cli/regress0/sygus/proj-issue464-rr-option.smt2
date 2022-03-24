; SCRUBBER: grep -v -E '\(define-fun'
; EXPECT: (error "SyGuS solution filtering requires the grammar to generate Boolean terms only")
; EXIT: 1
(set-logic ALL)
(set-option :global-declarations true)
(set-option :sygus-rr-synth-input true)
(set-option :sygus-filter-sol weak)
(declare-sort _u0 0)
(declare-const _x6 Bool)
(declare-const _x10 _u0)
(declare-const _x12 _u0)
(assert (= (distinct _x12 _x10) _x6))
(check-sat)
