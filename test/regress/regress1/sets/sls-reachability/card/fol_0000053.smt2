(set-logic ALL)

(set-info :status sat)

; forall b_bl:B. forall a_bk:A. B(b_bl & a_bk & ~f)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))

(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun b_bl () (Set Int))

(assert (set.subset b_bl UNIVERALSET))
(assert (>= (* 2 (set.card b_bl)) (+ (+ n (* 3 t)) 1)))

(declare-fun a_bk () (Set Int))

(assert (set.subset a_bk UNIVERALSET))
(assert (>= (set.card a_bk) (- n t)))


(assert
  (not
    (>=
      (* 2 (set.card (set.inter (set.inter b_bl a_bk) (set.minus UNIVERALSET f))))
      (+ (+ n (* 3 t)) 1))))

(check-sat)
