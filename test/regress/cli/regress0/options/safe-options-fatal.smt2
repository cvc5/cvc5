; DISABLE-TESTER: dump
; REQUIRES: no-competition
; EXPECT: (error "Fatal error in option parsing: expert option global-negate cannot be set in safe mode.")
; EXIT: 1
(set-logic ALL)
(set-option :safe-mode safe)
(set-option :global-negate true)
; should immediately terminate without running this check-sat
(check-sat)
