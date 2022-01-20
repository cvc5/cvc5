(set-logic ALL)

(set-info :status sat)

; forall c_ct:C. forall c_cs:C. nonempty(c_ct & c_cs & ~f)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))

(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun c_ct () (Set Int))

(assert (set.subset c_ct UNIVERALSET))
(assert (>= (* 2 (set.card c_ct)) (+ (- n t) 1)))

(declare-fun c_cs () (Set Int))

(assert (set.subset c_cs UNIVERALSET))
(assert (>= (* 2 (set.card c_cs)) (+ (- n t) 1)))


(assert
  (= (set.card (set.inter (set.inter c_ct c_cs) (set.minus UNIVERALSET f))) 0))

(check-sat)
