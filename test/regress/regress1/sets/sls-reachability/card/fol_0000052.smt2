(set-logic ALL)

(set-info :status sat)

; forall c_bj:C. forall b_bi:B. C(c_bj & b_bi & ~f)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))

(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun c_bj () (Set Int))

(assert (set.subset c_bj UNIVERALSET))
(assert (>= (* 2 (set.card c_bj)) (+ (- n t) 1)))

(declare-fun b_bi () (Set Int))

(assert (set.subset b_bi UNIVERALSET))
(assert (>= (* 2 (set.card b_bi)) (+ (+ n (* 3 t)) 1)))


(assert
  (not
    (>=
      (* 2 (set.card (set.inter (set.inter c_bj b_bi) (set.minus UNIVERALSET f))))
      (+ (- n t) 1))))

(check-sat)
