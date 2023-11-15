; REQUIRES: no-competition
; COMMAND-LINE: --safe-options --global-negate
; EXPECT-ERROR: (error "Error in option parsing: expert option global-negate cannot be set when safeOptions is true")
; EXPECT-ERROR:
; EXPECT-ERROR: Please use --help to get help on command-line options.
; EXIT: 1
; DISABLE-TESTER: dump
(set-logic ALL)
(check-sat)
