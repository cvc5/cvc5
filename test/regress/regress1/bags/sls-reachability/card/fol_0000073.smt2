(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status sat)

; forall c_cp:C. forall b_co:B. nonempty(c_cp & b_co & f & ~f)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun c_cp () (Bag Int))

(assert (bag.subbag c_cp UNIVERALSET))
(assert (>= (* 2 (bag.card c_cp)) (+ (- n t) 1)))

(declare-fun b_co () (Bag Int))

(assert (bag.subbag b_co UNIVERALSET))
(assert (>= (* 2 (bag.card b_co)) (+ (+ n (* 3 t)) 1)))


(assert
 (=
  (bag.card
   (bag.inter_min (bag.inter_min (bag.inter_min c_cp b_co) f)
                  (bag.difference_subtract UNIVERALSET f)))
  0))

(check-sat)
