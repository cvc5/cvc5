(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status sat)

; forall c_cv:C. forall b_cu:B. B(c_cv & b_cu & ~f)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun c_cv () (Bag Int))

(assert (bag.subbag c_cv UNIVERALSET))
(assert (>= (* 2 (bag.card c_cv)) (+ (- n t) 1)))

(declare-fun b_cu () (Bag Int))

(assert (bag.subbag b_cu UNIVERALSET))
(assert (>= (* 2 (bag.card b_cu)) (+ (+ n (* 3 t)) 1)))


(assert
 (not
  (>=
   (* 2
      (bag.card
       (bag.inter_min (bag.inter_min c_cv b_cu) (bag.difference_subtract UNIVERALSET f))))
   (+ (+ n (* 3 t)) 1))))

(check-sat)
