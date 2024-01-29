; COMMAND-LINE: --safe-options
; EXPECT: (error "Error in option parsing: expert option wf-checking cannot be set when safeOptions is true")
(set-logic ALL)
(set-option :wf-checking true)

