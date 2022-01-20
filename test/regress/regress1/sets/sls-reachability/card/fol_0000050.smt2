(set-logic ALL)

(set-info :status sat)

; forall b_bf:B. forall a_be:A. C(b_bf & a_be & f & ~f)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))

(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun b_bf () (Set Int))

(assert (set.subset b_bf UNIVERALSET))
(assert (>= (* 2 (set.card b_bf)) (+ (+ n (* 3 t)) 1)))

(declare-fun a_be () (Set Int))

(assert (set.subset a_be UNIVERALSET))
(assert (>= (set.card a_be) (- n t)))


(assert
  (not
    (>=
      (* 2
         (set.card
           (set.inter (set.inter (set.inter b_bf a_be) f) (set.minus UNIVERALSET f))))
      (+ (- n t) 1))))

(check-sat)
