; REQUIRES: no-competition
; COMMAND-LINE: --safe-mode=safe --global-negate
; EXPECT-ERROR: (error "Fatal error in option parsing: expert option global-negate cannot be set in safe mode.")
; EXIT: 1
; DISABLE-TESTER: dump
(set-logic ALL)
(check-sat)
