(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status sat)

; forall b_gg:B. forall b_gf:B. forall a_ge:A. forall a_gd:A. forall a_gc:A. top(b_gg & b_gf & a_ge & a_gd & a_gc)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun b_gg () (Bag Int))

(assert (bag.subbag b_gg UNIVERALSET))
(assert (>= (* 2 (bag.card b_gg)) (+ (+ n (* 3 t)) 1)))

(declare-fun b_gf () (Bag Int))

(assert (bag.subbag b_gf UNIVERALSET))
(assert (>= (* 2 (bag.card b_gf)) (+ (+ n (* 3 t)) 1)))

(declare-fun a_ge () (Bag Int))

(assert (bag.subbag a_ge UNIVERALSET))
(assert (>= (bag.card a_ge) (- n t)))

(declare-fun a_gd () (Bag Int))

(assert (bag.subbag a_gd UNIVERALSET))
(assert (>= (bag.card a_gd) (- n t)))

(declare-fun a_gc () (Bag Int))

(assert (bag.subbag a_gc UNIVERALSET))
(assert (>= (bag.card a_gc) (- n t)))


(assert
 (>=
  (bag.card
   (bag.difference_subtract UNIVERALSET
                            (bag.inter_min
                             (bag.inter_min (bag.inter_min (bag.inter_min b_gg b_gf) a_ge) a_gd) a_gc)))
  1))

(check-sat)
