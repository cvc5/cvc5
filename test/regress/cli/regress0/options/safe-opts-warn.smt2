; REQUIRES: no-competition
; COMMAND-LINE: --safe-options --no-fp-exp
; EXPECT-ERROR: (error "Error in option parsing: expert option fp-exp cannot be set when safeOptions is true. The value for fp-exp is already its current value (false). Omitting this option will avoid this exception.")
; EXPECT-ERROR:
; EXPECT-ERROR: Please use --help to get help on command-line options.
; EXIT: 1
; DISABLE-TESTER: dump
(set-logic ALL)
(check-sat)
