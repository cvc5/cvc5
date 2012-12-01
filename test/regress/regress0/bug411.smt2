; EXPECT: sat
; EXPECT: (define-fun x () Int 5)
; EXIT: 10
(set-option :produce-models true)
(set-logic QF_UFLIA)
(define-fun x () Int 5)
(check-sat)
(get-model)
