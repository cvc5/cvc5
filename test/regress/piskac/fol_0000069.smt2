(set-logic ALL)
(set-info :status sat)

; forall c_cb:C. forall a_ca:A. c_cb + a_ca + |~f| - 2n >= 1 or 1 <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))
(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun c_cb () Int)
(assert (<= c_cb n))
(assert (>= c_cb 0))
(assert (>= (* 2 c_cb) (+ (- n t) 1)))

(declare-fun a_ca () Int)
(assert (<= a_ca n))
(assert (>= a_ca 0))
(assert (>= a_ca (- n t)))


(assert (and (< (- (+ (+ c_cb a_ca) (set.card (set.minus UNIVERALSET f))) (* 2 n)) 1) (> 1 0)))

(check-sat)
