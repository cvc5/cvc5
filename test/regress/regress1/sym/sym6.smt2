(set-logic ALL)
(set-info :status sat)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)
(declare-fun w () Int)
(declare-fun u () Int)
(declare-fun v () Int)


(assert (= (+ w y u) (+ v z)))

(assert (> (+ x (* 2 y)) (+ u v)))

(assert (= (- x) (- (- y))))



(assert (or (< (+ x y z) 10) (> (+ v u) 10)))


(check-sat)

