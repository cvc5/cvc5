(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status sat)

; forall c_cr:C. forall b_cq:B. A(c_cr & b_cq & ~f)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun c_cr () (Bag Int))

(assert (bag.subbag c_cr UNIVERALSET))
(assert (>= (* 2 (bag.card c_cr)) (+ (- n t) 1)))

(declare-fun b_cq () (Bag Int))

(assert (bag.subbag b_cq UNIVERALSET))
(assert (>= (* 2 (bag.card b_cq)) (+ (+ n (* 3 t)) 1)))


(assert
 (not
  (>=
   (bag.card
    (bag.inter_min (bag.inter_min c_cr b_cq) (bag.difference_subtract UNIVERALSET f)))
   (- n t))))

(check-sat)
