(set-logic ALL)

(set-info :status sat)

; |~f| - 0 >= n or n <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))

(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))


(assert (and (< (- (set.card (set.minus UNIVERALSET f)) 0) n) (> n 0)))

(check-sat)
