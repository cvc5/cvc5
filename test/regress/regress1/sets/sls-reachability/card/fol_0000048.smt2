(set-logic ALL)

(set-info :status sat)

; forall b_ba:B. forall b_z:B. forall a_y:A. C(b_ba & b_z & a_y & ~f)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))

(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun b_ba () (Set Int))

(assert (set.subset b_ba UNIVERALSET))
(assert (>= (* 2 (set.card b_ba)) (+ (+ n (* 3 t)) 1)))

(declare-fun b_z () (Set Int))

(assert (set.subset b_z UNIVERALSET))
(assert (>= (* 2 (set.card b_z)) (+ (+ n (* 3 t)) 1)))

(declare-fun a_y () (Set Int))

(assert (set.subset a_y UNIVERALSET))
(assert (>= (set.card a_y) (- n t)))


(assert
  (not
    (>=
      (* 2
         (set.card
           (set.inter (set.inter (set.inter b_ba b_z) a_y) (set.minus UNIVERALSET f))))
      (+ (- n t) 1))))

(check-sat)
