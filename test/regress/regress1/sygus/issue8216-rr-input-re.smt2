; COMMAND-LINE: --sygus-rr-synth-input --sygus-abort-size=2
; EXPECT: (error "Maximum term size (2) for enumerative SyGuS exceeded.")
; SCRUBBER: grep -v -E '(\(define-fun'
(set-logic ALL)
(declare-fun a () String)
(assert (str.in_re (str.replace_re a (str.to_re "") a) (re.++ re.allchar (str.to_re "A"))))
(check-sat)
