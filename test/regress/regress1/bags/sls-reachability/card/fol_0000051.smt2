(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status sat)

; forall b_bh:B. forall a_bg:A. A(b_bh & a_bg & ~f)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun b_bh () (Bag Int))

(assert (bag.subbag b_bh UNIVERALSET))
(assert (>= (* 2 (bag.card b_bh)) (+ (+ n (* 3 t)) 1)))

(declare-fun a_bg () (Bag Int))

(assert (bag.subbag a_bg UNIVERALSET))
(assert (>= (bag.card a_bg) (- n t)))


(assert
 (not
  (>=
   (bag.card
    (bag.inter_min (bag.inter_min b_bh a_bg) (bag.difference_subtract UNIVERALSET f)))
   (- n t))))

(check-sat)
