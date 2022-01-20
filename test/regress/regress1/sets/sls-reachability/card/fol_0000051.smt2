(set-logic ALL)

(set-info :status sat)

; forall b_bh:B. forall a_bg:A. A(b_bh & a_bg & ~f)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))

(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun b_bh () (Set Int))

(assert (set.subset b_bh UNIVERALSET))
(assert (>= (* 2 (set.card b_bh)) (+ (+ n (* 3 t)) 1)))

(declare-fun a_bg () (Set Int))

(assert (set.subset a_bg UNIVERALSET))
(assert (>= (set.card a_bg) (- n t)))


(assert
  (not
    (>= (set.card (set.inter (set.inter b_bh a_bg) (set.minus UNIVERALSET f))) (- n t))))

(check-sat)
