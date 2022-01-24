(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status sat)

; forall c_ey:C. forall b_ex:B. forall b_ew:B. forall a_ev:A. forall a_eu:A. nonempty(c_ey & b_ex & b_ew & a_ev & a_eu & ~f)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun c_ey () (Bag Int))

(assert (bag.subbag c_ey UNIVERALSET))
(assert (>= (* 2 (bag.card c_ey)) (+ (- n t) 1)))

(declare-fun b_ex () (Bag Int))

(assert (bag.subbag b_ex UNIVERALSET))
(assert (>= (* 2 (bag.card b_ex)) (+ (+ n (* 3 t)) 1)))

(declare-fun b_ew () (Bag Int))

(assert (bag.subbag b_ew UNIVERALSET))
(assert (>= (* 2 (bag.card b_ew)) (+ (+ n (* 3 t)) 1)))

(declare-fun a_ev () (Bag Int))

(assert (bag.subbag a_ev UNIVERALSET))
(assert (>= (bag.card a_ev) (- n t)))

(declare-fun a_eu () (Bag Int))

(assert (bag.subbag a_eu UNIVERALSET))
(assert (>= (bag.card a_eu) (- n t)))


(assert
 (=
  (bag.card
   (bag.inter_min
    (bag.inter_min
     (bag.inter_min (bag.inter_min (bag.inter_min c_ey b_ex) b_ew) a_ev) a_eu)
    (bag.difference_subtract UNIVERALSET f)))
  0))

(check-sat)
