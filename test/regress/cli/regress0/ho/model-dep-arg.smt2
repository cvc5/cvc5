; COMMAND-LINE: --simplification=none
; EXPECT: unsat
;; introduces fresh Skolem in a trusted step
; DISABLE-TESTER: alethe
(set-logic HO_ALL)
(declare-fun f ((-> Int Int)) Int)
(declare-fun g (Int) Int)
(declare-fun h (Int) Int)
(assert (not (= (f (lambda ((x Int)) (+ 1 (f g)))) (f (lambda ((x Int)) (+ 1 (f h)))))))
(assert (= g h))
(check-sat)
