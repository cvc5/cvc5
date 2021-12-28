(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status sat)

; (n + 3t + 1) / 2 >= n or (n + 3t + 1) / 2 <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))


(assert (and (< (+ (+ n (* 3 t)) 1) (* 2 n)) (> (+ (+ n (* 3 t)) 1) (* 2 0))))

(check-sat)
