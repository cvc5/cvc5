(set-logic LIA)
(set-info :status unsat)

(declare-fun k_20 () Int)
(declare-fun k_72 () Int)
(declare-fun k_73 () Int)

(assert
(forall ((x1 Int) (x2 Int) (x3 Int) (x4 Int) (x5 Int) (x6 Int) (x7 Int) (x8 Int) (x9 Int) (x10 Int)) (not (>= (+ (* 3 x7) (* (- 1) (ite (= x7 k_20) k_72 k_73))) 1)) )
)

(check-sat)
