; COMMAND-LINE: --safe-options --global-negate
; EXPECT: (error "Error in option parsing: expert option global-negate cannot be set when safeOptions is true")
(set-logic ALL)
(check-sat)
