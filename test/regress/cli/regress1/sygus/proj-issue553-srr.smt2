; SCRUBBER: grep -v -E '.*'
; EXIT: 0
(set-logic NIRA)
(declare-const x Bool)
(assert x)
(find-synth :rewrite_input)
