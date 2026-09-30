; REQUIRES: safe-mode
; REQUIRES: no-competition
; DISABLE-TESTER: dump
; EXPECT: (error "Logic restricted in safe mode. Recursive function definitions are not supported in safe mode.")
; EXIT: 1
(set-logic UFLIA)
(define-fun-rec f ((x Int)) Int (ite (= x 0) 0 (f (- x 1))))
