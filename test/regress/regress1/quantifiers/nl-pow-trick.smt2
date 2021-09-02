; COMMAND-LINE: --cegqi-all --no-relational-triggers --no-sygus-inst
; EXPECT: unsat
(set-logic NIA)
(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun c () Int)
(define-fun s ((x Int)) Int (+ x 1))
(define-fun seq ((a Int) (b Int) (k Int) (x Int)) Bool ( = x (mod (+ 1 (* b (+ 1 k))) a)))
(define-fun power ((a Int) (b Int) (c Int)) Bool 
(exists ((x Int) (y Int)) (and (seq x y 0 1) (seq x y b c) (forall ((k Int) (z Int)) (=> (and (< k b) (seq x y k z)) (seq x y (+ 1 k) (* a z))))))
)
(assert (power 2 3 8))
(check-sat)
