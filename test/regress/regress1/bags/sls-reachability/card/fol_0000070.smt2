(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status unsat)

; forall c_ch:C. forall b_cg:B. nonempty(c_ch & b_cg & ~f)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun c_ch () (Bag Int))

(assert (bag.subbag c_ch UNIVERALSET))
(assert (>= (* 2 (bag.card c_ch)) (+ (- n t) 1)))

(declare-fun b_cg () (Bag Int))

(assert (bag.subbag b_cg UNIVERALSET))
(assert (>= (* 2 (bag.card b_cg)) (+ (+ n (* 3 t)) 1)))


(assert
 (=
  (bag.card
   (bag.inter_min (bag.inter_min c_ch b_cg) (bag.difference_subtract UNIVERALSET f)))
  0))

(check-sat)
