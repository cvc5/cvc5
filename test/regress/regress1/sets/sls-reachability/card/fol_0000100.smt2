(set-logic ALL)

(set-info :status sat)

; forall c_ey:C. forall b_ex:B. forall b_ew:B. forall a_ev:A. forall a_eu:A. nonempty(c_ey & b_ex & b_ew & a_ev & a_eu & ~f)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))

(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun c_ey () (Set Int))

(assert (set.subset c_ey UNIVERALSET))
(assert (>= (* 2 (set.card c_ey)) (+ (- n t) 1)))

(declare-fun b_ex () (Set Int))

(assert (set.subset b_ex UNIVERALSET))
(assert (>= (* 2 (set.card b_ex)) (+ (+ n (* 3 t)) 1)))

(declare-fun b_ew () (Set Int))

(assert (set.subset b_ew UNIVERALSET))
(assert (>= (* 2 (set.card b_ew)) (+ (+ n (* 3 t)) 1)))

(declare-fun a_ev () (Set Int))

(assert (set.subset a_ev UNIVERALSET))
(assert (>= (set.card a_ev) (- n t)))

(declare-fun a_eu () (Set Int))

(assert (set.subset a_eu UNIVERALSET))
(assert (>= (set.card a_eu) (- n t)))


(assert
  (=
    (set.card
      (set.inter
        (set.inter (set.inter (set.inter (set.inter c_ey b_ex) b_ew) a_ev) a_eu)
        (set.minus UNIVERALSET f)))
    0))

(check-sat)
