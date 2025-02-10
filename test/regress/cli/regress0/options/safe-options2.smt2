; REQUIRES: no-competition
; COMMAND-LINE: --safe-options --global-negate
; EXPECT-ERROR: (error "Fatal error in option parsing: expert option global-negate cannot be set when safe-options is true.")
; EXIT: 1
; DISABLE-TESTER: dump
(set-logic ALL)
(check-sat)
