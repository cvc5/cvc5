; COMMAND-LINE: -i
; EXPECT: unsat
(set-logic ALL)
(set-option :global-declarations true)
(define-fun y () Bool (> 0 0))
(assert y)
(push)
(check-sat)
