(set-logic ALL)
(set-info :status unsat)

; forall b_y:B. forall a_x:A. 2b_y + a_x + |~f| - 3n >= (n - t + 1) / 2 or (n - t + 1) / 2 <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))
(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun b_y () Int)
(assert (<= b_y n))
(assert (>= b_y 0))
(assert (>= (* 2 b_y) (+ (+ n (* 3 t)) 1)))

(declare-fun a_x () Int)
(assert (<= a_x n))
(assert (>= a_x 0))
(assert (>= a_x (- n t)))


(assert (and (< (* 2 (- (+ (+ (* 2 b_y) a_x) (set.card (set.minus UNIVERALSET f))) (* 3 n))) (+ (- n t) 1)) (> (+ (- n t) 1) (* 2 0))))

(check-sat)
