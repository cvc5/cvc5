(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status sat)

; forall c_e:C. c_e + |UNIVERALSET| - n >= n - t or n - t <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun c_e () Int)

(assert (<= c_e n))
(assert (>= c_e 0))
(assert (>= (* 2 c_e) (+ (- n t) 1)))


(assert (and (< (- (+ c_e (bag.card UNIVERALSET)) n) (- n t)) (> (- n t) 0)))

(check-sat)
