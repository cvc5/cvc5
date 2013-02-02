; EXPECT: sat
; EXPECT: (model
; EXPECT: (define-fun x () Int 5)
; EXPECT: )
; EXIT: 10
(set-option :produce-models true)
(set-logic QF_UFLIA)
(define-fun x () Int 5)
(check-sat)
(get-model)
