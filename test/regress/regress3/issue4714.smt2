; COMMAND-LINE: --check-models
; EXPECT: sat 
(set-logic UFNIRA)
(declare-fun c (Int) Int)
(define-fun d ((k Int)) Int (- (c k) 10))
(define-fun j ((k Int) (e Int)) Bool (<= 0 e (d k)))
(define-fun f ((k Int) (a Int) (b Int)) Int (ite (= b 1) a (mod a b)))
(define-fun g ((k Int) (a Int) (b Int)) Int (f k (* a (c b)) (c k)))
(define-fun h ((k Int) (a Int) (b Int)) Int (f k (+ a b) (c k)))
(assert (= (c 0) 1))
(assert (exists ((l Int) (k Int)) (and (j k l) (distinct (g k (h k l (g k l l)) l) (g k (h k l 0) l)))))
(check-sat)
