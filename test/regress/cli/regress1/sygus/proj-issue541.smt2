; SCRUBBER: grep -v -E '.*'
; EXIT: 1
(set-logic ALL)
(set-option :sygus-rr-synth-input true)
(assert (let ((_let0 (exists ((x Bool)) false))) (distinct _let0 _let0)))
(check-sat)
