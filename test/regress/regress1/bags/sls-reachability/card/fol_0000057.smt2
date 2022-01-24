(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status sat)

; forall a_bu:A. A(a_bu & ~f)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun a_bu () (Bag Int))

(assert (bag.subbag a_bu UNIVERALSET))
(assert (>= (bag.card a_bu) (- n t)))


(assert
 (not
  (>= (bag.card (bag.inter_min a_bu (bag.difference_subtract UNIVERALSET f))) (- n t))))

(check-sat)
