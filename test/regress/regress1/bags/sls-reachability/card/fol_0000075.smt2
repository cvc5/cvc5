(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status sat)

; forall c_ct:C. forall c_cs:C. nonempty(c_ct & c_cs & ~f)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun c_ct () (Bag Int))

(assert (bag.subbag c_ct UNIVERALSET))
(assert (>= (* 2 (bag.card c_ct)) (+ (- n t) 1)))

(declare-fun c_cs () (Bag Int))

(assert (bag.subbag c_cs UNIVERALSET))
(assert (>= (* 2 (bag.card c_cs)) (+ (- n t) 1)))


(assert
 (=
  (bag.card
   (bag.inter_min (bag.inter_min c_ct c_cs) (bag.difference_subtract UNIVERALSET f)))
  0))

(check-sat)
