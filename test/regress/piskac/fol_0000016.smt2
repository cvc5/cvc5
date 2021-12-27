(set-logic ALL)
(set-info :status unsat)

; (n - t + 1) / 2 >= n or n - t <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))
(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))


(assert (and (< (+ (- n t) 1) (* 2 n)) (> (- n t) 0)))

(check-sat)
