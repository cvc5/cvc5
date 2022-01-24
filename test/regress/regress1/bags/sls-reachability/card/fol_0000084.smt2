(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status sat)

; forall c_dm:C. forall a_dl:A. nonempty(c_dm & a_dl & ~f)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun c_dm () (Bag Int))

(assert (bag.subbag c_dm UNIVERALSET))
(assert (>= (* 2 (bag.card c_dm)) (+ (- n t) 1)))

(declare-fun a_dl () (Bag Int))

(assert (bag.subbag a_dl UNIVERALSET))
(assert (>= (bag.card a_dl) (- n t)))


(assert
 (=
  (bag.card
   (bag.inter_min (bag.inter_min c_dm a_dl) (bag.difference_subtract UNIVERALSET f)))
  0))

(check-sat)
