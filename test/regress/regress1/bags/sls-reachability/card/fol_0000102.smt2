(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status sat)

; forall c_fg:C. forall b_ff:B. forall b_fe:B. forall a_fd:A. nonempty(c_fg & b_ff & b_fe & a_fd & ~f)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun c_fg () (Bag Int))

(assert (bag.subbag c_fg UNIVERALSET))
(assert (>= (* 2 (bag.card c_fg)) (+ (- n t) 1)))

(declare-fun b_ff () (Bag Int))

(assert (bag.subbag b_ff UNIVERALSET))
(assert (>= (* 2 (bag.card b_ff)) (+ (+ n (* 3 t)) 1)))

(declare-fun b_fe () (Bag Int))

(assert (bag.subbag b_fe UNIVERALSET))
(assert (>= (* 2 (bag.card b_fe)) (+ (+ n (* 3 t)) 1)))

(declare-fun a_fd () (Bag Int))

(assert (bag.subbag a_fd UNIVERALSET))
(assert (>= (bag.card a_fd) (- n t)))


(assert
 (=
  (bag.card
   (bag.inter_min
    (bag.inter_min (bag.inter_min (bag.inter_min c_fg b_ff) b_fe) a_fd)
    (bag.difference_subtract UNIVERALSET f)))
  0))

(check-sat)
