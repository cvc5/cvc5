; COMMAND-LINE: --ext-rewrite-quant --sygus-inst -q
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(declare-fun c (Int) Bool)
(define-fun d ((e Int)) Bool (forall ((a Int) (b Int)) (! true :pattern ((c a) (c b)))))
(assert (exists ((e Int)) (distinct (d e) (= (ite (= e 0) (mod 0 e) 0) 0))))
(check-sat)
