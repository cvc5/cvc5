; DISABLE-TESTER: dump
; REQUIRES: no-competition
; COMMAND-LINE: --safe-options
; EXPECT: (error "Fatal error in option parsing: expert option wf-checking cannot be set when safe-options is true.")
; EXIT: 1
(set-logic ALL)
(set-option :wf-checking true)

