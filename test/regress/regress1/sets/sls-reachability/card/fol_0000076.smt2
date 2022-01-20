(set-logic ALL)

(set-info :status sat)

; forall c_cv:C. forall b_cu:B. B(c_cv & b_cu & ~f)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))

(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun c_cv () (Set Int))

(assert (set.subset c_cv UNIVERALSET))
(assert (>= (* 2 (set.card c_cv)) (+ (- n t) 1)))

(declare-fun b_cu () (Set Int))

(assert (set.subset b_cu UNIVERALSET))
(assert (>= (* 2 (set.card b_cu)) (+ (+ n (* 3 t)) 1)))


(assert
  (not
    (>=
      (* 2 (set.card (set.inter (set.inter c_cv b_cu) (set.minus UNIVERALSET f))))
      (+ (+ n (* 3 t)) 1))))

(check-sat)
