; SCRUBBER: grep -v -E '.*'
; EXIT: 0
(set-logic ALL)
(declare-const x Bool)
(set-option :sygus-fair direct)
(assert x)
(find-synth :rewrite_input)
