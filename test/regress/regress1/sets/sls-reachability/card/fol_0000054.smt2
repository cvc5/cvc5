(set-logic ALL)

(set-info :status sat)

; forall c_bn:C. forall a_bm:A. C(c_bn & a_bm & ~f)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))

(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun c_bn () (Set Int))

(assert (set.subset c_bn UNIVERALSET))
(assert (>= (* 2 (set.card c_bn)) (+ (- n t) 1)))

(declare-fun a_bm () (Set Int))

(assert (set.subset a_bm UNIVERALSET))
(assert (>= (set.card a_bm) (- n t)))


(assert
  (not
    (>=
      (* 2 (set.card (set.inter (set.inter c_bn a_bm) (set.minus UNIVERALSET f))))
      (+ (- n t) 1))))

(check-sat)
