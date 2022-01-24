(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status sat)

; forall b_fc:B. forall b_fb:B. forall a_fa:A. forall a_ez:A. nonempty(b_fc & b_fb & a_fa & a_ez & f & ~f)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun b_fc () (Bag Int))

(assert (bag.subbag b_fc UNIVERALSET))
(assert (>= (* 2 (bag.card b_fc)) (+ (+ n (* 3 t)) 1)))

(declare-fun b_fb () (Bag Int))

(assert (bag.subbag b_fb UNIVERALSET))
(assert (>= (* 2 (bag.card b_fb)) (+ (+ n (* 3 t)) 1)))

(declare-fun a_fa () (Bag Int))

(assert (bag.subbag a_fa UNIVERALSET))
(assert (>= (bag.card a_fa) (- n t)))

(declare-fun a_ez () (Bag Int))

(assert (bag.subbag a_ez UNIVERALSET))
(assert (>= (bag.card a_ez) (- n t)))


(assert
 (=
  (bag.card
   (bag.inter_min
    (bag.inter_min
     (bag.inter_min (bag.inter_min (bag.inter_min b_fc b_fb) a_fa) a_ez) f)
    (bag.difference_subtract UNIVERALSET f)))
  0))

(check-sat)
