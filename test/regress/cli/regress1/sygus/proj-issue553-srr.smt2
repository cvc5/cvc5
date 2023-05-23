; SCRUBBER: grep -v -E '.*'
; EXIT: 1
(set-logic NIRA)
(declare-const x Bool)
(set-option :sygus-rr-synth-input true)
(assert x)
(check-sat)
