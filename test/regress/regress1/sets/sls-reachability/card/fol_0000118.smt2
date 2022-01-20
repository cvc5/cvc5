(set-logic ALL)

(set-info :status unsat)

; forall a_hd:A. forall a_hc:A. forall a_hb:A. nonempty(a_hd & a_hc & a_hb & ~f)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))

(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun a_hd () (Set Int))

(assert (set.subset a_hd UNIVERALSET))
(assert (>= (set.card a_hd) (- n t)))

(declare-fun a_hc () (Set Int))

(assert (set.subset a_hc UNIVERALSET))
(assert (>= (set.card a_hc) (- n t)))

(declare-fun a_hb () (Set Int))

(assert (set.subset a_hb UNIVERALSET))
(assert (>= (set.card a_hb) (- n t)))


(assert
  (=
    (set.card
      (set.inter (set.inter (set.inter a_hd a_hc) a_hb) (set.minus UNIVERALSET f)))
    0))

(check-sat)
