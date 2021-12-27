(set-logic ALL)
(set-info :status sat)

; forall a_fg:A. 3a_fg + |~f| - 3n >= 1 or 1 <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))
(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun a_fg () Int)
(assert (<= a_fg n))
(assert (>= a_fg 0))
(assert (>= a_fg (- n t)))


(assert (and (< (- (+ (* 3 a_fg) (set.card (set.minus UNIVERALSET f))) (* 3 n)) 1) (> 1 0)))

(check-sat)
