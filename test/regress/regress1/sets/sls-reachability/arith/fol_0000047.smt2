(set-logic ALL)
(set-info :status unsat)

; forall b_w:B. forall a_v:A. b_w + a_v + |~f| - 2n >= (n - t + 1) / 2 or (n - t + 1) / 2 <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))
(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun b_w () Int)
(assert (<= b_w n))
(assert (>= b_w 0))
(assert (>= (* 2 b_w) (+ (+ n (* 3 t)) 1)))

(declare-fun a_v () Int)
(assert (<= a_v n))
(assert (>= a_v 0))
(assert (>= a_v (- n t)))


(assert (and (< (* 2 (- (+ (+ b_w a_v) (set.card (set.minus UNIVERALSET f))) (* 2 n))) (+ (- n t) 1)) (> (+ (- n t) 1) (* 2 0))))

(check-sat)
