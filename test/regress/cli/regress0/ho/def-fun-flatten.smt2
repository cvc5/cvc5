; EXPECT: unsat
;; HO not supported in Alethe
; DISABLE-TESTER: alethe
(set-logic HO_ALL)
(set-info :status unsat)
(declare-fun f (Int Int) Int)
(define-fun g ((x Int)) (-> Int Int) (f x))

(declare-fun a () Int)
(declare-fun b () Int)

(assert (not (= (g a b) (f a b))))

(check-sat)
