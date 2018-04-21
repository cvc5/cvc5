; COMMAND-LINE: --relational-triggers
; EXPECT: unsat
(set-logic ALL_SUPPORTED)
(set-info :status unsat)

(declare-sort U 0)

(declare-const k U)
(declare-const ff U) 
(declare-const ffk U)
(declare-fun fun1 (Int) Int)
(declare-fun fun2 (Int) Int)
(declare-fun c (U U) U)
(declare-fun app (U Int) Int)

(assert (forall ((f U) (g U)) (=> (forall ((x Int)) (= (app f x) (app g x))) (= f g))  ))

(assert (forall ((x Int)) (= (app ff x) (+ (fun1 x) (fun2 x)))))
(assert (forall ((x Int)) (= (app ffk x) (+ (fun1 (app k x)) (fun2 (app k x))))))

(assert (forall ((f U) (g U) (x Int)) (= (app (c f g) x) (app f (app g x)))))

(assert (not (= (c ff k) ffk)))

(check-sat)

