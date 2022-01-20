(set-logic ALL)

(set-info :status unsat)

; forall b_cb:B. C(b_cb & ~f)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))

(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun b_cb () (Set Int))

(assert (set.subset b_cb UNIVERALSET))
(assert (>= (* 2 (set.card b_cb)) (+ (+ n (* 3 t)) 1)))


(assert
  (not
    (>= (* 2 (set.card (set.inter b_cb (set.minus UNIVERALSET f)))) (+ (- n t) 1))))

(check-sat)
