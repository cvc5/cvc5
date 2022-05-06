; COMMAND-LINE: --fmf-fun
; EXPECT: sat
; DISABLE-TESTER: model
(set-logic ALL)
(define-fun-rec f ((x Int)) Bool false)
(assert (not (f 0)))
(check-sat)
