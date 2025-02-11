; DISABLE-TESTER: dump
; REQUIRES: no-competition
; EXPECT: (error "Fatal error in option parsing: expert option global-negate cannot be set when safe-options is true.")
; EXIT: 1
(set-logic ALL)
(set-option :safe-options true)
(set-option :global-negate true)
; should immediately terminate without running this check-sat
(check-sat)
