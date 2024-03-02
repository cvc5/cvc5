; COMMAND-LINE: --enum-inst
; EXPECT: unsat
;; HO not supported in Alethe
; DISABLE-TESTER: alethe
(set-logic HO_ALL)
(declare-fun f (Int Int) Int)
(assert (= f (lambda ((x Int) (y Int)) (+ 1 (f x y)))))
(check-sat)
