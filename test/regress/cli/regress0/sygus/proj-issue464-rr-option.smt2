; SCRUBBER: grep -v -E '.*'
; EXIT: 0
(set-logic ALL)
(set-option :global-declarations true)
(set-option :sygus-filter-sol weak)
(declare-sort _u0 0)
(declare-const _x6 Bool)
(declare-const _x10 _u0)
(declare-const _x12 _u0)
(assert (= (distinct _x12 _x10) _x6))
(find-synth :rewrite_input)
