(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status sat)

; forall c_dd:C. forall b_dc:B. forall a_db:A. top(c_dd & b_dc & a_db)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun c_dd () (Bag Int))

(assert (bag.subbag c_dd UNIVERALSET))
(assert (>= (* 2 (bag.card c_dd)) (+ (- n t) 1)))

(declare-fun b_dc () (Bag Int))

(assert (bag.subbag b_dc UNIVERALSET))
(assert (>= (* 2 (bag.card b_dc)) (+ (+ n (* 3 t)) 1)))

(declare-fun a_db () (Bag Int))

(assert (bag.subbag a_db UNIVERALSET))
(assert (>= (bag.card a_db) (- n t)))


(assert
 (>=
  (bag.card
   (bag.difference_subtract UNIVERALSET (bag.inter_min (bag.inter_min c_dd b_dc) a_db)))
  1))

(check-sat)
