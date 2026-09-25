; EXPECT: unsat
; Tests the Alethe translation of ARITH_TRICHOTOMY when the premises are
; negations of strict inequalities rather than non-strict inequalities.
(set-logic LIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (and (exists ((a Int) (b Int)) (= (+ (* 2 a) (* 2 b) 1) x)) (exists ((c Int) (d Int)) (= (+ (* 2 c) (* 2 d) 1) y))))
(assert (not (and (exists ((e Int) (a Int) (b Int)) (= (+ (* 2 e) (* 2 a) (* 2 b) 1) x)) (exists ((c Int) (f Int) (d Int)) (= y (+ (* 2 c) (* 2 f) (* 2 d) 1))))))
(check-sat)
