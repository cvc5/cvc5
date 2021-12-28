(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status sat)

; n - t >= n or n - t <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))


(assert (and (< (- n t) n) (> (- n t) 0)))

(check-sat)
