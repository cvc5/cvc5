(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status sat)

; forall b_ba:B. forall b_z:B. forall a_y:A. C(b_ba & b_z & a_y & ~f)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun b_ba () (Bag Int))

(assert (bag.subbag b_ba UNIVERALSET))
(assert (>= (* 2 (bag.card b_ba)) (+ (+ n (* 3 t)) 1)))

(declare-fun b_z () (Bag Int))

(assert (bag.subbag b_z UNIVERALSET))
(assert (>= (* 2 (bag.card b_z)) (+ (+ n (* 3 t)) 1)))

(declare-fun a_y () (Bag Int))

(assert (bag.subbag a_y UNIVERALSET))
(assert (>= (bag.card a_y) (- n t)))


(assert
 (not
  (>=
   (* 2
      (bag.card
       (bag.inter_min (bag.inter_min (bag.inter_min b_ba b_z) a_y)
                      (bag.difference_subtract UNIVERALSET f))))
   (+ (- n t) 1))))

(check-sat)
