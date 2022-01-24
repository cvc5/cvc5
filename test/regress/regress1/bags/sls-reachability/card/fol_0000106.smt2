(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status sat)

; forall b_fw:B. forall b_fv:B. forall a_fu:A. forall a_ft:A. C(b_fw & b_fv & a_fu & a_ft & ~f)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun b_fw () (Bag Int))

(assert (bag.subbag b_fw UNIVERALSET))
(assert (>= (* 2 (bag.card b_fw)) (+ (+ n (* 3 t)) 1)))

(declare-fun b_fv () (Bag Int))

(assert (bag.subbag b_fv UNIVERALSET))
(assert (>= (* 2 (bag.card b_fv)) (+ (+ n (* 3 t)) 1)))

(declare-fun a_fu () (Bag Int))

(assert (bag.subbag a_fu UNIVERALSET))
(assert (>= (bag.card a_fu) (- n t)))

(declare-fun a_ft () (Bag Int))

(assert (bag.subbag a_ft UNIVERALSET))
(assert (>= (bag.card a_ft) (- n t)))


(assert
 (not
  (>=
   (* 2
      (bag.card
       (bag.inter_min
        (bag.inter_min (bag.inter_min (bag.inter_min b_fw b_fv) a_fu) a_ft)
        (bag.difference_subtract UNIVERALSET f))))
   (+ (- n t) 1))))

(check-sat)
