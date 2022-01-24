(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status sat)

; forall c_bn:C. forall a_bm:A. C(c_bn & a_bm & ~f)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun c_bn () (Bag Int))

(assert (bag.subbag c_bn UNIVERALSET))
(assert (>= (* 2 (bag.card c_bn)) (+ (- n t) 1)))

(declare-fun a_bm () (Bag Int))

(assert (bag.subbag a_bm UNIVERALSET))
(assert (>= (bag.card a_bm) (- n t)))


(assert
 (not
  (>=
   (* 2
      (bag.card
       (bag.inter_min (bag.inter_min c_bn a_bm) (bag.difference_subtract UNIVERALSET f))))
   (+ (- n t) 1))))

(check-sat)
