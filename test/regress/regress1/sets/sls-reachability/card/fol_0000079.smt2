(set-logic ALL)

(set-info :status sat)

; forall c_dd:C. forall b_dc:B. forall a_db:A. top(c_dd & b_dc & a_db)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Set Int))
(declare-fun UNIVERALSET () (Set Int))

(assert (set.subset f UNIVERALSET))
(assert (= (set.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (set.card f) t))

(declare-fun c_dd () (Set Int))

(assert (set.subset c_dd UNIVERALSET))
(assert (>= (* 2 (set.card c_dd)) (+ (- n t) 1)))

(declare-fun b_dc () (Set Int))

(assert (set.subset b_dc UNIVERALSET))
(assert (>= (* 2 (set.card b_dc)) (+ (+ n (* 3 t)) 1)))

(declare-fun a_db () (Set Int))

(assert (set.subset a_db UNIVERALSET))
(assert (>= (set.card a_db) (- n t)))


(assert
  (>= (set.card (set.minus UNIVERALSET (set.inter (set.inter c_dd b_dc) a_db))) 1))

(check-sat)
