(set-logic ALL)
(set-info :status sat)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)
(declare-fun w () Int)
(declare-fun u () Int)
(declare-fun v () Int)

(declare-fun p (Int Int) Int)
(declare-fun A () (Set Int))


(assert (or (> (+ x y z) 3) (< (p x (+ (* 3 y) (* 3 z))) 5)))
(assert (set.subset A (set.insert y (set.singleton z))))



(check-sat)

