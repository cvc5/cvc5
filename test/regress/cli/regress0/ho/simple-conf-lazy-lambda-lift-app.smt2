; COMMAND-LINE: --uf-lazy-ll
; EXPECT: unsat
(set-logic HO_ALL)
(set-info :status unsat)
(define-fun f ((x Int)) Int (+ x 1))
(declare-fun g (Int) Int)
(declare-fun h (Int) Int)

(assert (or (= f g) (= f h)))

(assert (= (g 4) 0))
(assert (= (h 4) 8))

(check-sat)
