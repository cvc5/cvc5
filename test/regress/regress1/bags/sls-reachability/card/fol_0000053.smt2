(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status sat)

; forall b_bl:B. forall a_bk:A. B(b_bl & a_bk & ~f)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun b_bl () (Bag Int))

(assert (bag.subbag b_bl UNIVERALSET))
(assert (>= (* 2 (bag.card b_bl)) (+ (+ n (* 3 t)) 1)))

(declare-fun a_bk () (Bag Int))

(assert (bag.subbag a_bk UNIVERALSET))
(assert (>= (bag.card a_bk) (- n t)))


(assert
 (not
  (>=
   (* 2
      (bag.card
       (bag.inter_min (bag.inter_min b_bl a_bk) (bag.difference_subtract UNIVERALSET f))))
   (+ (+ n (* 3 t)) 1))))

(check-sat)
