; COMMAND-LINE: --enum-inst
; EXPECT: unsat
(set-logic HO_ALL)
(declare-fun f (Int Int) Int)
(declare-fun g (Int Int) Int)
(assert (or (= g (lambda ((x Int) (y Int)) (+ 1 (f y x)))) (= g (lambda ((x Int) (y Int)) (+ 2 (f y x))))))
(assert (or (= f (lambda ((x Int) (y Int)) (+ 1 (g y x)))) (= f (lambda ((x Int) (y Int)) (+ 2 (g y x))))))
(check-sat)
