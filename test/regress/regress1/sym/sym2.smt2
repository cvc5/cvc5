(set-logic ALL)
(set-info :status sat)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)
(declare-fun w () Int)
(declare-fun u () Int)
(declare-fun v () Int)


(assert (> (- (+ (* 3 x) (* 3 y) (* 3 z)) u v) 0))
(assert (> (+ u v) 0))
(assert (> (+ x y) 0))
(assert (> x 0))
(assert (> z 0))
(assert (> u 0))
(assert (> v 0))
(assert (< u 10))
(assert (< v 10))





(check-sat)

