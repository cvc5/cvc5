; COMMAND-LINE: --ext-rewrite-quant -q
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(define-fun f ((a Int) (b Int)) Int (ite (= b 0) 0 a))
(assert (exists ((c Int)) (distinct (f c (mod 0 0)) 0)))
(check-sat)
