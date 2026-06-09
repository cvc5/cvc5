; COMMAND-LINE: --incremental
; EXPECT: unknown
; EXPECT: unknown
(set-option :global-declarations true)
(set-logic ALL)
(define-fun-rec b () Bool b)
(define-funs-rec ((g ((x Bool)) Bool)) (b))
(check-sat)
(reset-assertions)
(assert (not b))
(check-sat)
