; EXPECT: unsat
; EXPECT: (error "recursive function definitions require a logic with quantifiers")
; EXIT: 1
(set-logic UFBV)
(define-funs-rec ((f ((b Bool)) Bool) (g ((b Bool)) Bool)) (b b))
(assert (g false))
(check-sat)
(reset)
(set-logic QF_BV)
(define-funs-rec ((f ((b Bool)) Bool) (g ((b Bool)) Bool)) (b b))
(assert (g false))
(check-sat)
