; COMMAND-LINE: --incremental
; EXPECT: unsat
; EXPECT: unsat
; EXPECT: unsat
(set-logic UF)
(set-option :global-declarations true)

(push)
(define-const a Bool true)
(define-fun f ((b Bool)) Bool b)
(define-const a2 Bool true)

(define-fun a3 () Bool true)

(define-fun-rec b () Bool true)
(define-funs-rec ((g ((b Bool)) Bool)) (b))
(assert (or (not a) (not a2) (not a3) (not b) (g false)))
(check-sat)
(pop)

(assert (or (not a) (not a2) (not a3) (not b) (g false)))
(check-sat)

(reset-assertions)

(assert (or (not a) (not a2) (not a3) (not b) (g false)))
(check-sat)
