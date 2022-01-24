(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status sat)

; forall a_v:A. forall a_u:A. C(a_v & a_u & ~f)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun a_v () (Bag Int))

(assert (bag.subbag a_v UNIVERALSET))
(assert (>= (bag.card a_v) (- n t)))

(declare-fun a_u () (Bag Int))

(assert (bag.subbag a_u UNIVERALSET))
(assert (>= (bag.card a_u) (- n t)))


(assert
 (not
  (>=
   (* 2
      (bag.card
       (bag.inter_min (bag.inter_min a_v a_u) (bag.difference_subtract UNIVERALSET f))))
   (+ (- n t) 1))))

(check-sat)
