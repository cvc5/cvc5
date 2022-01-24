(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status unsat)

; forall b_bq:B. forall a_bp:A. forall a_bo:A. C(b_bq & a_bp & a_bo)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun b_bq () (Bag Int))

(assert (bag.subbag b_bq UNIVERALSET))
(assert (>= (* 2 (bag.card b_bq)) (+ (+ n (* 3 t)) 1)))

(declare-fun a_bp () (Bag Int))

(assert (bag.subbag a_bp UNIVERALSET))
(assert (>= (bag.card a_bp) (- n t)))

(declare-fun a_bo () (Bag Int))

(assert (bag.subbag a_bo UNIVERALSET))
(assert (>= (bag.card a_bo) (- n t)))


(assert
 (not
  (>= (* 2 (bag.card (bag.inter_min (bag.inter_min b_bq a_bp) a_bo))) (+ (- n t) 1))))

(check-sat)
