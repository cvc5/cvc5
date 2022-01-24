(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status sat)

; forall c_bd:C. forall b_bc:B. forall a_bb:A. C(c_bd & b_bc & a_bb & ~f)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun c_bd () (Bag Int))

(assert (bag.subbag c_bd UNIVERALSET))
(assert (>= (* 2 (bag.card c_bd)) (+ (- n t) 1)))

(declare-fun b_bc () (Bag Int))

(assert (bag.subbag b_bc UNIVERALSET))
(assert (>= (* 2 (bag.card b_bc)) (+ (+ n (* 3 t)) 1)))

(declare-fun a_bb () (Bag Int))

(assert (bag.subbag a_bb UNIVERALSET))
(assert (>= (bag.card a_bb) (- n t)))


(assert
 (not
  (>=
   (* 2
      (bag.card
       (bag.inter_min (bag.inter_min (bag.inter_min c_bd b_bc) a_bb)
                      (bag.difference_subtract UNIVERALSET f))))
   (+ (- n t) 1))))

(check-sat)
