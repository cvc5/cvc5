(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status unsat)

; forall b_cb:B. C(b_cb & ~f)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun b_cb () (Bag Int))

(assert (bag.subbag b_cb UNIVERALSET))
(assert (>= (* 2 (bag.card b_cb)) (+ (+ n (* 3 t)) 1)))


(assert
 (not
  (>=
   (* 2 (bag.card (bag.inter_min b_cb (bag.difference_subtract UNIVERALSET f))))
   (+ (- n t) 1))))

(check-sat)
