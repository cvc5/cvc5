(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status sat)

; forall a_gi:A. forall a_gh:A. C(a_gi & a_gh & ~f)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun a_gi () (Bag Int))

(assert (bag.subbag a_gi UNIVERALSET))
(assert (>= (bag.card a_gi) (- n t)))

(declare-fun a_gh () (Bag Int))

(assert (bag.subbag a_gh UNIVERALSET))
(assert (>= (bag.card a_gh) (- n t)))


(assert
 (not
  (>=
   (* 2
      (bag.card
       (bag.inter_min (bag.inter_min a_gi a_gh) (bag.difference_subtract UNIVERALSET f))))
   (+ (- n t) 1))))

(check-sat)
