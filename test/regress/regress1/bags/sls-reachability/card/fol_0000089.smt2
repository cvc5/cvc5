(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status unsat)

; forall b_du:B. forall a_dt:A. nonempty(b_du & a_dt & ~f)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun b_du () (Bag Int))

(assert (bag.subbag b_du UNIVERALSET))
(assert (>= (* 2 (bag.card b_du)) (+ (+ n (* 3 t)) 1)))

(declare-fun a_dt () (Bag Int))

(assert (bag.subbag a_dt UNIVERALSET))
(assert (>= (bag.card a_dt) (- n t)))


(assert
 (=
  (bag.card
   (bag.inter_min (bag.inter_min b_du a_dt) (bag.difference_subtract UNIVERALSET f)))
  0))

(check-sat)
