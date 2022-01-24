(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status unsat)

; forall a_hd:A. forall a_hc:A. forall a_hb:A. nonempty(a_hd & a_hc & a_hb & ~f)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun a_hd () (Bag Int))

(assert (bag.subbag a_hd UNIVERALSET))
(assert (>= (bag.card a_hd) (- n t)))

(declare-fun a_hc () (Bag Int))

(assert (bag.subbag a_hc UNIVERALSET))
(assert (>= (bag.card a_hc) (- n t)))

(declare-fun a_hb () (Bag Int))

(assert (bag.subbag a_hb UNIVERALSET))
(assert (>= (bag.card a_hb) (- n t)))


(assert
 (=
  (bag.card
   (bag.inter_min (bag.inter_min (bag.inter_min a_hd a_hc) a_hb)
                  (bag.difference_subtract UNIVERALSET f)))
  0))

(check-sat)
