; REQUIRES: safe-mode
; REQUIRES: no-competition
; DISABLE-TESTER: dump
; EXPECT: (error "Logic restricted in safe mode. Recursive function definitions are not supported in safe mode.")
; EXIT: 1
(set-logic UFLIA)
(define-funs-rec ((f ((x Int)) Int) (g ((x Int)) Int)) ((g x) (f x)))
