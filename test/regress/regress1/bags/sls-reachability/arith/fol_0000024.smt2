(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status sat)

; forall c_g:C. c_g + |UNIVERALSET| - n >= (n + 3t + 1) / 2 or (n + 3t + 1) / 2 <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun c_g () Int)

(assert (<= c_g n))
(assert (>= c_g 0))
(assert (>= (* 2 c_g) (+ (- n t) 1)))


(assert
 (and (< (* 2 (- (+ c_g (bag.card UNIVERALSET)) n)) (+ (+ n (* 3 t)) 1))
      (> (+ (+ n (* 3 t)) 1) (* 2 0))))

(check-sat)
