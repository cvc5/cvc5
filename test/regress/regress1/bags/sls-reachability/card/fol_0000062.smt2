(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status sat)

; forall c_by:C. C(c_by & ~f)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun c_by () (Bag Int))

(assert (bag.subbag c_by UNIVERALSET))
(assert (>= (* 2 (bag.card c_by)) (+ (- n t) 1)))


(assert
 (not
  (>=
   (* 2 (bag.card (bag.inter_min c_by (bag.difference_subtract UNIVERALSET f))))
   (+ (- n t) 1))))

(check-sat)
