; REQUIRES: stable-mode
; REQUIRES: no-competition
; DISABLE-TESTER: dump
; EXPECT: (error "Logic restricted in stable mode. Pool declarations are only supported in unrestricted mode.")
; EXIT: 1
(set-logic ALL)
(declare-pool P Int (0 1))
