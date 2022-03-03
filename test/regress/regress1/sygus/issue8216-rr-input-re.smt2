; COMMAND-LINE: --sygus-rr-synth-input --sygus-abort-size=1
; SCRUBBER: grep -v -E '(\(define-fun'
; EXIT: 1
(set-logic ALL)
(declare-fun a () String)
(assert (str.in_re (str.replace_re a (str.to_re "") a) (re.++ re.allchar (str.to_re "A"))))
(check-sat)
