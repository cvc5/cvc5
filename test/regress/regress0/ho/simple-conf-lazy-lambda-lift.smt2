; COMMAND-LINE: --uf-lazy-ll
; EXPECT: unsat
(set-logic HO_ALL)
(set-info :status unsat)
(define-fun f ((x Int)) Int (+ x 1))
(define-fun g ((x Int)) Int (+ x 2))
(define-fun h ((x Int)) Int 6)

(assert (or (= f g) (= f h)))

(check-sat)
