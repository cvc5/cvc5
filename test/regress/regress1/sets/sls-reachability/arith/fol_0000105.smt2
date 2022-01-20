(set-logic ALL)
(set-info :status sat)

; forall b_en:B. forall a_em:A. 2b_en + 2a_em + |~f| - 4n >= (n + 3t + 1) / 2 or (n + 3t + 1) / 2 <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))
(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun b_en () Int)
(assert (<= b_en n))
(assert (>= b_en 0))
(assert (>= (* 2 b_en) (+ (+ n (* 3 t)) 1)))

(declare-fun a_em () Int)
(assert (<= a_em n))
(assert (>= a_em 0))
(assert (>= a_em (- n t)))


(assert (and (< (* 2 (- (+ (+ (* 2 b_en) (* 2 a_em)) (set.card (set.minus UNIVERALSET f))) (* 4 n))) (+ (+ n (* 3 t)) 1)) (> (+ (+ n (* 3 t)) 1) (* 2 0))))

(check-sat)
