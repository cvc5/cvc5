; DISABLE-TESTER: dump
; REQUIRES: no-competition
; COMMAND-LINE: --safe-mode=safe
; EXPECT: (error "Fatal error in option parsing: expert option wf-checking cannot be set when safe mode is enabled.")
; EXIT: 1
(set-logic ALL)
(set-option :wf-checking true)

