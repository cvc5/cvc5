; SCRUBBER: grep -v -E '.*'
; EXIT: 0
(set-logic ALL)
(declare-sort u 0)
(declare-sort _u 0)
(declare-const x (Array _u u))
(assert (distinct x x))
(find-synth :rewrite_input)
