; COMMAND-LINE: --full-saturate-quant --ee-mode=distributed
; COMMAND-LINE: --full-saturate-quant --ee-mode=central
; EXPECT: unsat
(set-logic ALL)
(declare-fun o (Int) Int)
(declare-fun f (Int Int) Int)
(assert (forall ((x Int)) (forall ((y Int)) (! (= 1 (* y (div y y))) :pattern ((f x y))))))
(assert (= 0 (f (o 0) (o 1))))
(check-sat)
