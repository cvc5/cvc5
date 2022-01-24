(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status sat)

; forall b_et:B. forall b_es:B. forall b_er:B. forall a_eq:A. forall a_ep:A. nonempty(b_et & b_es & b_er & a_eq & a_ep & ~f)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun b_et () (Bag Int))

(assert (bag.subbag b_et UNIVERALSET))
(assert (>= (* 2 (bag.card b_et)) (+ (+ n (* 3 t)) 1)))

(declare-fun b_es () (Bag Int))

(assert (bag.subbag b_es UNIVERALSET))
(assert (>= (* 2 (bag.card b_es)) (+ (+ n (* 3 t)) 1)))

(declare-fun b_er () (Bag Int))

(assert (bag.subbag b_er UNIVERALSET))
(assert (>= (* 2 (bag.card b_er)) (+ (+ n (* 3 t)) 1)))

(declare-fun a_eq () (Bag Int))

(assert (bag.subbag a_eq UNIVERALSET))
(assert (>= (bag.card a_eq) (- n t)))

(declare-fun a_ep () (Bag Int))

(assert (bag.subbag a_ep UNIVERALSET))
(assert (>= (bag.card a_ep) (- n t)))


(assert
 (=
  (bag.card
   (bag.inter_min
    (bag.inter_min
     (bag.inter_min (bag.inter_min (bag.inter_min b_et b_es) b_er) a_eq) a_ep)
    (bag.difference_subtract UNIVERALSET f)))
  0))

(check-sat)
