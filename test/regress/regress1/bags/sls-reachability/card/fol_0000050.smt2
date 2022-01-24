(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status sat)

; forall b_bf:B. forall a_be:A. C(b_bf & a_be & f & ~f)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun b_bf () (Bag Int))

(assert (bag.subbag b_bf UNIVERALSET))
(assert (>= (* 2 (bag.card b_bf)) (+ (+ n (* 3 t)) 1)))

(declare-fun a_be () (Bag Int))

(assert (bag.subbag a_be UNIVERALSET))
(assert (>= (bag.card a_be) (- n t)))


(assert
 (not
  (>=
   (* 2
      (bag.card
       (bag.inter_min (bag.inter_min (bag.inter_min b_bf a_be) f)
                      (bag.difference_subtract UNIVERALSET f))))
   (+ (- n t) 1))))

(check-sat)
