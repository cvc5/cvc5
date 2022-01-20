(set-logic ALL)
(set-info :status unsat)

; |~f| - 0 >= (n - t + 1) / 2 or (n - t + 1) / 2 <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))
(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))


(assert (and (< (* 2 (- (set.card (set.minus UNIVERALSET f)) 0)) (+ (- n t) 1)) (> (+ (- n t) 1) (* 2 0))))

(check-sat)
