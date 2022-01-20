(set-logic ALL)

(set-info :status sat)

; forall b_fc:B. forall b_fb:B. forall a_fa:A. forall a_ez:A. nonempty(b_fc & b_fb & a_fa & a_ez & f & ~f)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))

(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun b_fc () (Set Int))

(assert (set.subset b_fc UNIVERALSET))
(assert (>= (* 2 (set.card b_fc)) (+ (+ n (* 3 t)) 1)))

(declare-fun b_fb () (Set Int))

(assert (set.subset b_fb UNIVERALSET))
(assert (>= (* 2 (set.card b_fb)) (+ (+ n (* 3 t)) 1)))

(declare-fun a_fa () (Set Int))

(assert (set.subset a_fa UNIVERALSET))
(assert (>= (set.card a_fa) (- n t)))

(declare-fun a_ez () (Set Int))

(assert (set.subset a_ez UNIVERALSET))
(assert (>= (set.card a_ez) (- n t)))


(assert
  (=
    (set.card
      (set.inter
        (set.inter (set.inter (set.inter (set.inter b_fc b_fb) a_fa) a_ez) f)
        (set.minus UNIVERALSET f)))
    0))

(check-sat)
