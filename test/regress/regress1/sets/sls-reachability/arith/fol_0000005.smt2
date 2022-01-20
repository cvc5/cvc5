(set-logic ALL)
(set-info :status sat)

; n - t = (n - t + 1) / 2

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))
(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))


(assert (not (= (* 2 (- n t)) (+ (- n t) 1))))

(check-sat)
