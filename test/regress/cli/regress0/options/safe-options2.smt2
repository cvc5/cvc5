; REQUIRES: no-competition
; COMMAND-LINE: --safe-mode=safe --global-negate
; EXPECT-ERROR: (error "Fatal error in option parsing: expert option global-negate cannot be set when safe mode is enabled.")
; EXIT: 1
; DISABLE-TESTER: dump
(set-logic ALL)
(check-sat)
