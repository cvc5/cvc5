; DISABLE-TESTER: dump
; REQUIRES: no-competition
; COMMAND-LINE: --safe-mode=stable
; EXPECT: (error "Fatal error in option parsing: expert option wf-checking cannot be set in stable mode.")
; EXIT: 1
(set-logic ALL)
(set-option :wf-checking true)
