(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status unsat)

; forall a_gj:A. C(a_gj & ~f)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun a_gj () (Bag Int))

(assert (bag.subbag a_gj UNIVERALSET))
(assert (>= (bag.card a_gj) (- n t)))


(assert
 (not
  (>=
   (* 2 (bag.card (bag.inter_min a_gj (bag.difference_subtract UNIVERALSET f))))
   (+ (- n t) 1))))

(check-sat)
