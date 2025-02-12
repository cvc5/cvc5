; REQUIRES: no-competition
; COMMAND-LINE: --safe-options --no-fp-exp
; EXPECT-ERROR: (error "Fatal error in option parsing: expert option fp-exp cannot be set when safe-options is true. The value for fp-exp is already its current value (false). Omitting this option may avoid this exception.")
; EXIT: 1
; DISABLE-TESTER: dump
(set-logic ALL)
(check-sat)
