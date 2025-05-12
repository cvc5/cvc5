; DISABLE-TESTER: dump
; REQUIRES: no-competition
<<<<<<< HEAD
; EXPECT: (error "Fatal error in option parsing: expert option global-negate cannot be set when safe mode is enabled.")
=======
; EXPECT: (error "Fatal error in option parsing: expert option global-negate cannot be set in safe mode.")
>>>>>>> 9170d48eba55450ab08ef6f0e545d4b2fa4ecadb
; EXIT: 1
(set-logic ALL)
(set-option :safe-mode safe)
(set-option :global-negate true)
; should immediately terminate without running this check-sat
(check-sat)
