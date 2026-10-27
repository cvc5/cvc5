; COMMAND-LINE: --sygus-abort-size=1
; SCRUBBER: grep -v -E '\(define-fun'
; EXPECT: (error "Maximum term size (1) for enumerative SyGuS exceeded.")
; EXIT: 1
(set-logic ALL)
(declare-fun a () String)
(assert (str.in_re (str.replace_re a (str.to_re "") a) (re.++ re.allchar (str.to_re "A"))))
(find-synth :rewrite_input)
