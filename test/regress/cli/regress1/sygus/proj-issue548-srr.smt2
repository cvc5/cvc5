; SCRUBBER: grep -v -E '.*'
; EXIT: 1
(set-logic ALL)
(declare-const x Bool)
(set-option :sygus-fair direct)
(set-option :sygus-rr-synth-input true)
(assert x)
(check-sat)
