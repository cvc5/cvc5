(set-logic ALL)
(set-info :status unsat)

; forall c_bh:C. forall b_bg:B. c_bh + b_bg + |~f| - 2n >= (n - t + 1) / 2 or (n - t + 1) / 2 <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))
(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun c_bh () Int)
(assert (<= c_bh n))
(assert (>= c_bh 0))
(assert (>= (* 2 c_bh) (+ (- n t) 1)))

(declare-fun b_bg () Int)
(assert (<= b_bg n))
(assert (>= b_bg 0))
(assert (>= (* 2 b_bg) (+ (+ n (* 3 t)) 1)))


(assert (and (< (* 2 (- (+ (+ c_bh b_bg) (set.card (set.minus UNIVERALSET f))) (* 2 n))) (+ (- n t) 1)) (> (+ (- n t) 1) (* 2 0))))

(check-sat)
