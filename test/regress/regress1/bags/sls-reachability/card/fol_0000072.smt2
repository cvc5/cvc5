(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status sat)

; forall c_cn:C. forall c_cm:C. forall b_cl:B. nonempty(c_cn & c_cm & b_cl & ~f)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun c_cn () (Bag Int))

(assert (bag.subbag c_cn UNIVERALSET))
(assert (>= (* 2 (bag.card c_cn)) (+ (- n t) 1)))

(declare-fun c_cm () (Bag Int))

(assert (bag.subbag c_cm UNIVERALSET))
(assert (>= (* 2 (bag.card c_cm)) (+ (- n t) 1)))

(declare-fun b_cl () (Bag Int))

(assert (bag.subbag b_cl UNIVERALSET))
(assert (>= (* 2 (bag.card b_cl)) (+ (+ n (* 3 t)) 1)))


(assert
 (=
  (bag.card
   (bag.inter_min (bag.inter_min (bag.inter_min c_cn c_cm) b_cl)
                  (bag.difference_subtract UNIVERALSET f)))
  0))

(check-sat)
