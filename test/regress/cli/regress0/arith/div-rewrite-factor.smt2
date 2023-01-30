(set-logic QF_LIA)
(set-info :status unsat)
(declare-fun x () Int)
(declare-fun y () Int)

(assert (not (= (div (+ (* 2 x) (* (- 2) y)) 2) (- x y))))

(check-sat)
