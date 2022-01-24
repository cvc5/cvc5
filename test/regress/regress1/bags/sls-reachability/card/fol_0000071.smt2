(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status sat)

; forall c_ck:C. forall b_cj:B. forall b_ci:B. nonempty(c_ck & b_cj & b_ci & ~f)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun c_ck () (Bag Int))

(assert (bag.subbag c_ck UNIVERALSET))
(assert (>= (* 2 (bag.card c_ck)) (+ (- n t) 1)))

(declare-fun b_cj () (Bag Int))

(assert (bag.subbag b_cj UNIVERALSET))
(assert (>= (* 2 (bag.card b_cj)) (+ (+ n (* 3 t)) 1)))

(declare-fun b_ci () (Bag Int))

(assert (bag.subbag b_ci UNIVERALSET))
(assert (>= (* 2 (bag.card b_ci)) (+ (+ n (* 3 t)) 1)))


(assert
 (=
  (bag.card
   (bag.inter_min (bag.inter_min (bag.inter_min c_ck b_cj) b_ci)
                  (bag.difference_subtract UNIVERALSET f)))
  0))

(check-sat)
